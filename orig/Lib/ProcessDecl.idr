module Lib.ProcessDecl

import Data.IORef
import Data.String
import Data.Vect
import Data.List
import Data.Maybe

import Lib.Elab
import Lib.Parser
import Lib.Syntax
import Lib.TopContext
import Lib.Eval
import Lib.Types
import Lib.Util
import Lib.Erasure

dumpEnv : Context -> M String
dumpEnv ctx =
  unlines . reverse <$> go (names ctx) 0 (reverse $ zip ctx.env (toList ctx.types)) []
  where
    isVar : Nat -> Val -> Bool
    isVar k (VVar _ k' [<]) = k == k'
    isVar _ _ = False

    go : List String -> Nat -> List (Val, String, Val) -> List String -> M (List String)
    go _ _ [] acc = pure acc
    go names k ((v, n, ty) :: xs) acc = if isVar k v
      -- TODO - use Doc and add <+/> as appropriate to printing
      then go names (S k) xs ("  \{n} : \{pprint names !(quote ctx.lvl ty)}":: acc)
      else go names (S k) xs ("  \{n} = \{pprint names !(quote ctx.lvl v)} : \{pprint names !(quote ctx.lvl ty)}":: acc)

export
logMetas : Nat -> M ()
logMetas mstart = do
  -- FIXME, now this isn't logged for Sig / Data.
  top <- get
  mc <- readIORef top.metaCtx
  let mlen = length mc.metas `minus` mstart
  for_ (reverse $ take mlen mc.metas) $ \case
    (Solved fc k soln) => do
      -- TODO put a flag on this, vscode is getting overwhelmed and
      -- dropping errors
      --info fc "solve \{show k} as \{pprint [] !(quote 0 soln)}"
      pure ()
    (Unsolved fc k ctx ty User cons) => do
      ty' <- quote ctx.lvl ty
      let names = (toList $ map fst ctx.types)
      env <- dumpEnv ctx
      let msg = "\{env}  -----------\n  \{pprint names ty'}"
      info fc "User Hole\n\{msg}"

    (Unsolved fc k ctx ty kind cons) => do
      tm <- quote ctx.lvl !(forceMeta ty)
      -- Now that we're collecting errors, maybe we simply check at the end
      -- TODO - log constraints?
      -- FIXME in Combinatory, the val doesn't match environment?
      let msg = "Unsolved meta \{show k} \{show kind} type \{pprint (names ctx) tm} \{show $ length cons} constraints"
      msgs <- for cons $ \ (MkMc fc env sp val) => do
            pure "  * (m\{show k} (\{unwords $ map show $ sp <>> []}) =?= \{show val}"
      sols <- case kind of
        AutoSolve => do
          x <- quote ctx.lvl ty
          ty <- eval ctx.env CBN x
          debug "AUTO ---> \{show ty}"
          -- we want the context here too.
          top <- get
          -- matches <- case !(contextMatches ctx ty) of
          --   [] => findMatches ctx ty $ toList top.defs
          --   xs => pure xs
          matches <- findMatches ctx ty $ toList top.defs
          -- TODO try putting mc into TopContext for to see if it gives better terms
          pure $ ["  \{show $ length matches} Solutions: \{show matches}"]
          -- pure $ "  \{show $ length matches} Solutions:" :: map (("  " ++) . interpolate . pprint (names ctx) . fst) matches

        _ => pure []
      info fc $ unlines ([msg] ++ msgs ++ sols)
      -- addError $ E fc $ unlines ([msg] ++ msgs ++ sols)


-- Used for Class and Record
getSigs : List Decl -> List (FC, String, Raw)
getSigs [] = []
getSigs ((TypeSig _ [] _) :: xs) = getSigs xs
getSigs ((TypeSig fc (nm :: nms) ty) :: xs) = (fc, nm, ty) :: getSigs xs
getSigs (_ :: xs) = getSigs xs

teleToPi : Telescope -> Raw -> Raw
teleToPi [] end = end
teleToPi ((info, ty) :: tele) end = RPi (getFC info) info ty (teleToPi tele end)

impTele : Telescope -> Telescope
impTele tele = map (\(BI fc nm _ quant, ty) => (BI fc nm Implicit Zero, ty)) tele


export
processDecl : List String -> Decl -> M ()

-- REVIEW I supposed I could have updated top here instead of the dance with the parser...
processDecl ns  (PMixFix{})  = pure ()

processDecl ns  (TypeSig fc names tm) = do
  putStrLn "-----"

  top <- get
  mc <- readIORef top.metaCtx
  let mstart = length mc.metas
  for_ names $ \nm => do
    let Nothing := lookupRaw nm top
      | Just entry => error fc "\{show nm} is already defined at \{show entry.fc}"
    pure ()
  ty <- check (mkCtx fc) tm (VU fc)
  ty <- zonk top 0 [] ty
  putStrLn "TypeSig \{unwords names} : \{pprint [] ty}"
  for_ names $ \nm => setDef (QN ns nm) fc ty Axiom
  -- Zoo4eg has metas in TypeSig, need to decide if I want to support leaving them unsolved here
  -- logMetas mstart

processDecl ns (PType fc nm ty) = do
  top <- get
  ty' <- check (mkCtx fc) (maybe (RU fc) id ty) (VU fc)
  setDef (QN ns nm) fc ty' PrimTCon

processDecl ns  (PFunc fc nm uses ty src) = do
  top <- get
  ty <- check (mkCtx fc) ty (VU fc)
  ty' <- nf [] ty
  putStrLn "pfunc \{nm} : \{pprint [] ty'} := \{show src}"
  -- TODO wire through fc?
  for_ uses $ \ name => case lookupRaw name top of
    Nothing => error fc "\{name} not in scope"
    _ => pure ()
  setDef (QN ns nm) fc ty' (PrimFn src uses)

processDecl ns (Def fc nm clauses) = do
  putStrLn "-----"
  putStrLn "Def \{show nm}"
  top <- get
  mc <- readIORef top.metaCtx
  let mstart = length mc.metas
  let Just entry = lookupRaw nm top
    | Nothing => throwError $ E fc "No declaration for \{nm}"
  let (MkEntry fc name ty Axiom) := entry
    | _ => throwError $ E fc "\{nm} already defined at \{show entry.fc}"

  putStrLn "check \{nm} at \{pprint [] ty}"
  vty <- eval empty CBN ty

  debug "\{nm} vty is \{show vty}"


  -- I can take LHS apart syntactically or elaborate it with an infer
  clauses' <- traverse (makeClause top) clauses
  tm <- buildTree (mkCtx fc) (MkProb clauses' vty)
  -- putStrLn "Ok \{pprint [] tm}"

  mc <- readIORef top.metaCtx
  let mlen = length mc.metas `minus` mstart
  solveAutos mstart
  -- TODO - make nf that expands all metas and drop zonk
  -- Day1.newt is a test case
  -- tm' <- nf [] tm
  tm' <- zonk top 0 [] tm
  when top.verbose $ putStrLn "NF\n\{render 80 $ pprint[] tm'}"
  -- TODO we want to keep both versions, but this is checking in addition to erasing
  -- currently CompileExp is also doing erasure.
  -- TODO we need erasure info on the lambdas or to fake up an appropriate environment
  -- and erase inside. Currently the checking is imprecise
  tm'' <- erase [] tm' []
  when top.verbose $ putStrLn "ERASED\n\{render 80 $ pprint[] tm'}"
  debug "Add def \{nm} \{pprint [] tm'} : \{pprint [] ty}"
  updateDef (QN ns nm) fc ty (Fn tm')
  -- logMetas mstart

processDecl ns (DCheck fc tm ty) = do
  putStrLn "----- DCheck"
  top <- get

  putStrLn "INFO at \{show fc}: check \{show tm} at \{show ty}"
  ty' <- check (mkCtx fc) ty (VU fc)
  putStrLn "  got type \{pprint [] ty'}"
  vty <- eval [] CBN ty'
  res <- check (mkCtx fc) tm vty
  putStrLn "  got \{pprint [] res}"
  norm <- nf [] res
  putStrLn "  NF \{pprint [] norm}"
  norm <- nfv [] res
  putStrLn "  NFV \{pprint [] norm}"

processDecl ns (Class classFC nm tele decls) = do
  -- REVIEW maybe we can leverage Record for this
  -- a couple of catches, we don't want the dotted accessors and
  -- the self argument should be an auto-implicit
  putStrLn "-----"
  putStrLn "Class \{nm}"
  let fields = getSigs decls
  -- We'll need names for the telescope
  let dcName = "Mk\{nm}"
  let tcType = teleToPi tele (RU classFC)
  let tail = foldl (\ acc, (BI fc nm icit _, _) => RApp fc acc (RVar fc nm) icit) (RVar classFC nm) tele
  let dcType = teleToPi (impTele tele) $
    foldr (\(fc, nm, ty), acc =>  RPi fc (BI fc nm Explicit Many) ty acc  ) tail fields

  putStrLn "tcon type \{pretty tcType}"
  putStrLn "dcon type \{pretty dcType}"
  let decl = Data classFC nm tcType [TypeSig classFC [dcName] dcType]
  putStrLn "Decl:"
  putStrLn $ render 90 $ pretty decl
  processDecl ns decl
  for_ fields $ \ (fc,name,ty) => do
      let funType = teleToPi (impTele tele) $ RPi fc (BI fc "_" Auto Many) tail ty
      let autoPat = foldl (\acc, (fc,nm,ty) => RApp fc acc (RVar fc nm) Explicit) (RVar classFC dcName) fields
      let lhs = foldl (\acc, (BI fc' nm icit quant, _) => RApp fc' acc (RVar fc' nm) Implicit) (RVar fc name) tele
      let lhs = RApp classFC lhs autoPat Auto
      let decl = Def fc name [(lhs, (RVar fc name))]

      putStrLn "\{name} : \{pretty funType}"
      putStrLn "\{pretty decl}"
      processDecl ns $ TypeSig fc [name] funType
      processDecl ns decl


processDecl ns (Instance instfc ty decls) = do

  putStrLn "-----"
  putStrLn "Instance \{pretty ty}"
  top <- get
  let tyFC = getFC ty

  vty <- check (mkCtx instfc) ty (VU instfc)
  -- Here `tele` holds arguments to the instance
  let (codomain, tele) = splitTele vty
  -- env represents the environment of those arguments
  let env = tenv (length tele)
  debug "codomain \{pprint [] codomain}"
  debug "tele is \{show tele}"

  -- ok so we need a name, a hack for now.
  -- Maybe we need to ask the user (e.g. `instance someName : Monad Foo where`)
  -- or use "Monad\{show $ length defs}"
  let instname = interpolate $ pprint [] codomain
  let sigDecl = TypeSig instfc [instname] ty
  -- This needs to be declared before processing the defs, but the defs need to be
  -- declared before this - side effect is that a duplicate def is noted at the first
  -- member
  case lookupRaw instname top of
    Just _ => pure MkUnit -- TODO check that the types match
    Nothing => processDecl ns sigDecl

  let (Just decls) = collectDecl <$> decls
    | _ => do
      debug "Forward declaration \{show sigDecl}"

  let (Ref _ tconName _, args) := funArgs codomain
    | (tm, _) => error tyFC "\{pprint [] codomain} doesn't appear to be a TCon application"
  let (Just (MkEntry _ name type (TCon cons))) = lookup tconName top
    | _ => error tyFC "\{tconName} is not a type constructor"
  let [con] = cons
    | _ => error tyFC "\{tconName} has multiple constructors \{show cons}"
  let (Just (MkEntry _ _ dcty (DCon _ _))) = lookup con top
    | _ => error tyFC "can't find constructor \{show con}"
  vdcty@(VPi _ nm icit rig a b) <- eval [] CBN dcty
    | x => error (getFC x) "dcty not Pi"
  debug "dcty \{pprint [] dcty}"
  let (_,args) = funArgs codomain

  debug "traverse \{show $ map showTm args}"
  -- This is a little painful because we're reverse engineering the
  -- individual types back out from the composite type
  args' <- traverse (eval env CBN) args
  debug "args' is \{show args'}"
  conTele <- getFields !(apply vdcty args') env []
  -- declare individual functions, collect their defs
  defs <- for conTele $ \case
     (MkBinder fc nm Explicit rig ty) => do
       let ty' = foldr (\(MkBinder fc nm' icit rig ty'), acc => Pi fc nm' icit rig ty' acc) ty tele
       let nm' = "\{instname},\{nm}"
       -- we're working with a Tm, so we define directly instead of processDecl
       let Just (Def fc name xs) = find (\case (Def y name xs) => name == nm; _ => False) decls
          | _ => error instfc "no definition for \{nm}"

       setDef (QN ns nm') fc ty' Axiom
       let decl = (Def fc nm' xs)
       putStrLn "***"
       putStrLn "«\{nm'}» : \{pprint [] ty'}"
       putStrLn $ render 80 $ pretty decl
       pure $ Just decl
     _ => pure Nothing

  for_ (mapMaybe id defs) $ \decl => do
    -- debug because already printed above, but nice to have it near processing
    debug $ render 80 $ pretty decl
    processDecl ns decl
  let (QN _ con') = con
  let decl = Def instfc instname [(RVar instfc instname, mkRHS instname conTele (RVar instfc con'))]
  putStrLn "SIGDECL"
  putStrLn "\{pretty sigDecl}"
  putStrLn $ render 80 $ pretty decl
  processDecl ns decl
  where
    -- try to extract types of individual fields from the typeclass dcon
    -- We're assuming they don't depend on each other.
    getFields : Val -> Env -> List Binder -> M (List Binder)
    getFields tm@(VPi fc nm Explicit rig ty sc) env bnds = do
      bnd <- MkBinder fc nm Explicit rig <$> quote (length env) ty
      getFields !(sc $$ VVar fc (length env) [<]) env (bnd :: bnds)
    getFields tm@(VPi fc nm _ rig ty sc) env bnds = getFields !(sc $$ VVar fc (length env) [<]) env bnds
    getFields tm xs bnds = pure $ reverse bnds

    tenv : Nat -> Env
    tenv Z = []
    tenv (S k) = (VVar emptyFC k [<] :: tenv k)

    mkRHS : String -> List Binder -> Raw -> Raw
    mkRHS instName (MkBinder fc nm Explicit rig ty :: bs) tm = mkRHS instName bs (RApp fc tm (RVar fc "\{instName},\{nm}") Explicit)
    mkRHS instName (b :: bs) tm = mkRHS instName bs tm
    mkRHS instName [] tm = tm

    apply : Val -> List Val -> M Val
    apply x [] = pure x
    apply (VPi fc nm icit rig a b) (x :: xs) = apply !(b $$ x) xs
    apply x (y :: xs) = error instfc "expected pi type \{show x}"

processDecl ns (ShortData fc lhs sigs) = do
  (nm,args) <- getArgs lhs []
  let ty = foldr (\ (fc,n), a => (RPi fc (BI fc n Explicit Zero) (RU fc) a)) (RU fc) args
  cons <- traverse (mkDecl args []) sigs
  let dataDecl = Data fc nm ty cons
  putStrLn "SHORTDATA"
  putStrLn "\{pretty dataDecl}"
  processDecl ns dataDecl
  where
    getArgs : Raw -> List (FC, String) -> M (String, List (FC, String))
    getArgs (RVar fc1 nm) acc = pure (nm, acc)
    getArgs (RApp _ t (RVar fc' nm) _) acc = getArgs t ((fc', nm) :: acc)
    getArgs tm _ = error (getFC tm) "Expected contructor application, got: \{show tm}"

    mkDecl : List (FC, Name) -> List Raw -> Raw -> M Decl
    mkDecl args acc (RVar fc' name) = do
      let base = foldr (\ ty, acc => RPi (getFC ty) (BI (getFC ty) "_" Explicit Many) ty acc) lhs acc
      let ty = foldr (\ (fc,nm), acc => RPi fc (BI fc nm Implicit Zero) (RU fc) acc) base args
      pure $ TypeSig fc' [name] ty
    mkDecl args acc (RApp fc' t u icit) = mkDecl args (u :: acc) t
    mkDecl args acc tm = error (getFC tm) "Expected contructor application, got: \{show tm}"

processDecl ns (Data fc nm ty cons) = do
  putStrLn "-----"
  putStrLn "Data \{nm}"
  top <- get
  mc <- readIORef top.metaCtx
  tyty <- check (mkCtx fc) ty (VU fc)
  case lookupRaw nm top of
    Just (MkEntry _ name type Axiom) => do
      unifyCatch fc (mkCtx fc) !(eval [] CBN tyty) !(eval [] CBN type)
    Just (MkEntry _ name type _) => error fc "\{show nm} already declared"
    Nothing => setDef (QN ns nm) fc tyty Axiom
  cnames <- for cons $ \x => case x of
      (TypeSig fc names tm) => do
          debug "check dcon \{show names} \{show tm}"
          dty <- check (mkCtx fc) tm (VU fc)
          debug "dty \{show names} is \{pprint [] dty}"

          -- We only check that codomain uses the right type constructor
          -- We know it's in U because it's part of a checked Pi type
          let (codomain, tele) = splitTele dty
          -- for printing
          let tnames = reverse $ map (\(MkBinder _ nm _ _ _) => nm) tele
          let (Ref _ hn _, args) := funArgs codomain
            | (tm, _) => error (getFC tm) "expected \{nm} got \{pprint tnames tm}"
          when (hn /= QN ns nm) $
            error (getFC codomain) "Constructor codomain is \{pprint tnames codomain} rather than \{nm}"

          for_ names $ \ nm' => do
            setDef (QN ns nm') fc dty (DCon (getArity dty) hn)
          pure $ map (QN ns) names
      decl => throwError $ E (getFC decl) "expected constructor declaration"
  putStrLn "setDef \{nm}  TCon \{show $ join cnames}"
  updateDef (QN ns nm) fc tyty (TCon (join cnames))
  -- logMetas mstart
  where
    checkDeclType : Tm -> M ()
    checkDeclType (UU _) = pure ()
    checkDeclType (Pi _ str icit rig t u) = checkDeclType u
    checkDeclType _ = error fc "data type doesn't return U"

processDecl ns (Record recordFC nm tele cname decls) = do
  putStrLn "-----"
  putStrLn "Record"
  let fields = getSigs decls
  let dcName = fromMaybe "Mk\{nm}" cname
  let tcType = teleToPi tele (RU recordFC)
  -- REVIEW - I probably want to stick the telescope in front of the fields
  let tail = foldl (\ acc, (BI fc nm icit _, _) => RApp fc acc (RVar fc nm) icit) (RVar recordFC nm) tele
  let dcType = teleToPi (impTele tele) $
    foldr (\(fc, nm, ty), acc =>  RPi fc (BI fc nm Explicit Many) ty acc  ) tail fields

  putStrLn "tcon type \{pretty tcType}"
  putStrLn "dcon type \{pretty dcType}"
  let decl = Data recordFC nm tcType [TypeSig recordFC [dcName] dcType]
  putStrLn "Decl:"
  putStrLn $ render 90 $ pretty decl
  processDecl ns decl
  for_ fields $ \ (fc,name,ty) => do
    -- TODO dependency isn't handled yet
    -- we'll need to replace stuff like `len` with `len self`.
    let funType = teleToPi (impTele tele) $ RPi fc (BI fc "_" Explicit Many) tail ty
    let autoPat = foldl (\acc, (fc,nm,ty) => RApp fc acc (RVar fc nm) Explicit) (RVar recordFC dcName) fields

    -- `fieldName` - consider dropping to keep namespace clean
    -- let lhs = foldl (\acc, (BI fc' nm icit quant, _) => RApp fc' acc (RVar fc' nm) Implicit) (RVar fc name) tele
    -- let lhs = RApp recordFC lhs autoPat Explicit
    -- let decl = Def fc name [(lhs, (RVar fc name))]
    -- putStrLn "\{name} : \{pretty funType}"
    -- putStrLn "\{pretty decl}"
    -- processDecl ns $ TypeSig fc [name] funType
    -- processDecl ns decl

    -- `.fieldName`
    let pname = "." ++ name
    let lhs = foldl (\acc, (BI fc' nm icit quant, _) => RApp fc' acc (RVar fc' nm) Implicit) (RVar fc pname) tele
    let lhs = RApp recordFC lhs autoPat Explicit
    let pdecl = Def fc pname [(lhs, (RVar fc name))]
    putStrLn "\{pname} : \{pretty funType}"
    putStrLn "\{pretty pdecl}"
    processDecl ns $ TypeSig fc [pname] funType
    processDecl ns pdecl
