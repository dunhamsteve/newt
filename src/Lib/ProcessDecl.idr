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

-- Check that the arguments are not explicit and the type constructor in codomain matches
-- Later we will build a table of codomain type, and maybe make the user tag the candidates
-- like Idris does with %hint
isCandidate : Val -> Tm -> Bool
isCandidate ty (Pi fc nm Explicit rig t u) = False
isCandidate ty (Pi fc nm icit rig t u) = isCandidate ty u
isCandidate (VRef _ nm _ _) (Ref fc nm' def) = nm == nm'
isCandidate ty (App fc t u) = isCandidate ty t
isCandidate _ _ = False

-- This is a crude first pass
-- TODO consider ctx
findMatches : Context -> Val -> List TopEntry -> M (List (Tm, MetaContext))
findMatches ctx ty [] = pure []
findMatches ctx ty ((MkEntry name type def) :: xs) = do
  let True = isCandidate ty type | False => findMatches ctx ty xs
  top <- get
  -- let ctx = mkCtx (getFC ty)
  -- FIXME we're restoring state, but the INFO logs have already been emitted
  -- Also redo this whole thing to run during elab, recheck constraints, etc.
  mc <- readIORef top.metas
  catchError {e=Error} (do
      -- TODO sort out the FC here
      let fc = getFC ty
      debug "TRY \{name} : \{pprint [] type} for \{show ty}"
      -- This check is solving metas, so we save mc below in case we want this solution
      -- tm <- check (mkCtx fc) (RVar fc name) ty
      tm <- check ctx (RVar fc name) ty
      debug "Found \{pprint [] tm} for \{show ty}"
      mc' <- readIORef top.metas
      writeIORef top.metas mc
      ((tm, mc') ::) <$> findMatches ctx ty xs)
    (\ err => do
      debug "No match \{show ty} \{pprint [] type} \{showError "" err}"
      writeIORef top.metas mc
      findMatches ctx ty xs)

contextMatches : Context -> Val -> M (List (Tm, MetaContext))
contextMatches ctx ty = go (zip ctx.env (toList ctx.types))
  where
    go : List (Val, String, Val) -> M (List (Tm, MetaContext))
    go [] = pure []
    go ((tm, nm, vty) :: xs) = do
      type <- quote ctx.lvl vty
      let True = isCandidate ty type | False => go xs
      top <- get
      mc <- readIORef top.metas
      catchError {e=Error} (do
          debug "TRY context \{nm} : \{pprint (names ctx) type} for \{show ty}"
          unifyCatch (getFC ty) ctx ty vty
          mc' <- readIORef top.metas
          writeIORef top.metas mc
          tm <- quote ctx.lvl tm
          ((tm, mc') ::) <$> go xs)
        (\ err => do
          debug "No match \{show ty} \{pprint (names ctx) type} \{showError "" err}"
          writeIORef top.metas mc
          go xs)

-- FIXME - decide if we want to count Zero here
getArity : Tm -> Nat
getArity (Pi x str icit rig t u) = S (getArity u)
-- Ref or App (of type constructor) are valid
getArity _ = Z

-- Can metas live in context for now?
-- We'll have to be able to add them, which might put gamma in a ref



-- Makes the arg for `solve` when we solve an auto
makeSpine : Nat -> Vect k BD -> SnocList Val
makeSpine k [] = [<]
makeSpine (S k) (Defined :: xs) = makeSpine k xs
makeSpine (S k) (Bound :: xs) = makeSpine k xs :< VVar emptyFC k [<]
makeSpine 0 xs = ?fixme

solveAutos : Nat -> List MetaEntry -> M ()
solveAutos mlen [] = pure ()
solveAutos mlen ((Unsolved fc k ctx ty AutoSolve _) :: es) = do
      debug "AUTO solving \{show k} : \{show ty}"
      -- we want the context here too.
      top <- get
      [(tm, mc)] <- case !(contextMatches ctx ty) of
            [] => findMatches ctx ty top.defs
            xs => pure xs
        | res => do
          debug "FAILED to solve \{show ty}, matches: \{commaSep $ map (pprint [] . fst) res}"
          solveAutos mlen es
        -- | res => error fc "FAILED to solve \{show ty}, matches: \{show $ map (pprint [] . fst) res}"
      writeIORef top.metas mc
      val <- eval ctx.env CBN tm
      debug "SOLUTION \{pprint [] tm} evaled to \{show val}"
      let sp = makeSpine ctx.lvl ctx.bds
      solve ctx.env k sp val
      mc <- readIORef top.metas
      solveAutos mlen (take mlen mc.metas)
solveAutos mlen (_ :: es) = solveAutos mlen es

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
  mc <- readIORef top.metas
  let mlen = length mc.metas `minus` mstart
  for_ (reverse $ take mlen mc.metas) $ \case
    (Solved fc k soln) => info fc "solve \{show k} as \{pprint [] !(quote 0 soln)}"
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
      addError $ E fc $ unlines ([msg] ++ msgs)


export
processDecl : Decl -> M ()

-- REVIEW I supposed I could have updated top here instead of the dance with the parser...
processDecl (PMixFix{})  = pure ()

processDecl (TypeSig fc names tm) = do
  putStrLn "-----"

  top <- get
  mc <- readIORef top.metas
  let mstart = length mc.metas
  for_ names $ \nm => do
    let Nothing := lookup nm top
      | _ => error fc "\{show nm} is already defined"
    pure ()
  ty <- check (mkCtx fc) tm (VU fc)
  putStrLn "TypeSig \{unwords names} : \{pprint [] ty}"
  debug "got \{pprint [] ty}"
  for_ names $ \nm => setDef nm fc ty Axiom
  -- Zoo4eg has metas in TypeSig, need to decide if I want to support leaving them unsolved here
  -- logMetas mstart

processDecl (PType fc nm ty) = do
  top <- get
  ty' <- check (mkCtx fc) (maybe (RU fc) id ty) (VU fc)
  setDef nm fc ty' PrimTCon

processDecl (PFunc fc nm uses ty src) = do
  top <- get
  ty <- check (mkCtx fc) ty (VU fc)
  ty' <- nf [] ty
  putStrLn "pfunc \{nm} : \{pprint [] ty'} := \{show src}"
  -- TODO wire through fc?
  for_ uses $ \ name => case lookup name top of
    Nothing => error fc "\{name} not in scope"
    _ => pure ()
  setDef nm fc ty' (PrimFn src uses)

processDecl (Def fc nm clauses) = do
  putStrLn "-----"
  putStrLn "Def \{show nm}"
  top <- get
  mc <- readIORef top.metas
  let mstart = length mc.metas
  let Just entry = lookup nm top
    | Nothing => throwError $ E fc "No declaration for \{nm}"
  let (MkEntry name ty Axiom) := entry
    | _ => throwError $ E fc "\{nm} already defined"

  putStrLn "check \{nm} at \{pprint [] ty}"
  vty <- eval empty CBN ty

  debug "\{nm} vty is \{show vty}"


  -- I can take LHS apart syntactically or elaborate it with an infer
  clauses' <- traverse (makeClause top) clauses
  tm <- buildTree (mkCtx fc) (MkProb clauses' vty)
  -- putStrLn "Ok \{pprint [] tm}"

  mc <- readIORef top.metas
  let mlen = length mc.metas `minus` mstart
  solveAutos mlen (take mlen mc.metas)
  -- TODO - make nf that expands all metas and drop zonk
  -- Day1.newt is a test case
  -- tm' <- nf [] tm
  tm' <- zonk top 0 [] tm
  putStrLn "NF\n\{render 80 $ pprint[] tm'}"
  -- TODO we want to keep both versions, but this is checking in addition to erasing
  -- currently CompileExp is also doing erasure.
  -- TODO we need erasure info on the lambdas or to fake up an appropriate environment
  -- and erase inside. Currently the checking is imprecise
  tm'' <- erase [] tm' []
  putStrLn "ERASED\n\{render 80 $ pprint[] tm'}"
  debug "Add def \{nm} \{pprint [] tm'} : \{pprint [] ty}"
  updateDef nm fc ty (Fn tm')
  -- logMetas mstart

processDecl (DCheck fc tm ty) = do
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

processDecl (Class classFC nm tele decls) = do
  putStrLn "-----"
  putStrLn "Class \{nm}"
  let fields = getSigs decls
  -- We'll need names for the telescope
  let dcName = "Mk\{nm}"
  let tcType = teleToPi tele (RU classFC)
  let tail = foldl (\ acc, (BI fc nm icit _, _) => RApp fc acc (RVar fc nm) icit) (RVar classFC nm) tele
  let dcType = teleToPi impTele $
    foldr (\(fc, nm, ty), acc =>  RPi fc (BI fc nm Explicit Many) ty acc  ) tail fields

  putStrLn "tcon type \{pretty tcType}"
  putStrLn "dcon type \{pretty dcType}"
  let decl = Data classFC nm tcType [TypeSig classFC [dcName] dcType]
  putStrLn "Decl:"
  putStrLn $ render 90 $ pretty decl
  processDecl decl
  for_ fields $ \ (fc,name,ty) => do
      let funType = teleToPi impTele $ RPi fc (BI fc "_" Auto Many) tail ty
      let autoPat = foldl (\acc, (fc,nm,ty) => RApp fc acc (RVar fc nm) Explicit) (RVar classFC dcName) fields
      let lhs = foldl (\acc, (BI fc' nm icit quant, _) => RApp fc' acc (RVar fc' nm) Implicit) (RVar fc name) tele
      let lhs = RApp classFC lhs autoPat Auto
      let decl = Def fc name [(lhs, (RVar fc name))]

      putStrLn "\{name} : \{pretty funType}"
      putStrLn "\{pretty decl}"
      processDecl $ TypeSig fc [name] funType
      processDecl decl
  where

    getSigs : List Decl -> List (FC, String, Raw)
    getSigs [] = []
    getSigs ((TypeSig _ [] _) :: xs) = getSigs xs
    getSigs ((TypeSig fc (nm :: nms) ty) :: xs) = (fc, nm, ty) :: getSigs xs
    getSigs (_:: xs) = getSigs xs

    impTele : Telescope
    impTele = map (\(BI fc nm _ quant, ty) => (BI fc nm Implicit Zero, ty)) tele

    teleToPi : Telescope -> Raw -> Raw
    teleToPi [] end = end
    teleToPi ((info, ty) :: tele) end = RPi (getFC info) info ty (teleToPi tele end)

processDecl (Instance instfc ty decls) = do
  let decls = collectDecl decls
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

  let (Ref _ tconName _, args) := funArgs codomain
    | (tm, _) => error tyFC "\{pprint [] codomain} doesn't appear to be a TCon application"
  let (Just (MkEntry name type (TCon cons))) = lookup tconName top
    | _ => error tyFC "\{tconName} is not a type constructor"
  let [con] = cons
    | _ => error tyFC "\{tconName} has multiple constructors \{show cons}"
  let (Just (MkEntry _ dcty (DCon _ _))) = lookup con top
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
     (MkBind fc nm Explicit rig ty) => do
       let ty' = foldr (\(MkBind fc nm' icit rig ty'), acc => Pi fc nm' icit rig ty' acc) ty tele
       let nm' = "\{instname},\{nm}"
       -- we're working with a Tm, so we define directly instead of processDecl
       setDef nm' fc ty' Axiom
       let Just (Def fc name xs) = find (\case (Def y name xs) => name == nm; _ => False) decls
          | _ => error instfc "no definition for \{nm}"

       let decl = (Def fc nm' xs)
       putStrLn "***"
       putStrLn "«\{nm'}» : \{pprint [] ty'}"
       putStrLn $ render 80 $ pretty decl
       pure $ Just decl
     _ => pure Nothing
  -- This needs to be declared before processing the defs, but the defs need to be
  -- declared before this
  processDecl sigDecl
  for_ (mapMaybe id defs) $ \decl => do
    -- debug because already printed above, but nice to have it near processing
    debug $ render 80 $ pretty decl
    processDecl decl

  let decl = Def instfc instname [(RVar instfc instname, mkRHS instname conTele (RVar instfc con))]
  putStrLn "SIGDECL"
  putStrLn "\{pretty sigDecl}"
  putStrLn $ render 80 $ pretty decl
  processDecl decl
  where
    -- try to extract types of individual fields from the typeclass dcon
    -- We're assuming they don't depend on each other.
    getFields : Val -> Env -> List Binder -> M (List Binder)
    getFields tm@(VPi fc nm Explicit rig ty sc) env bnds = do
      bnd <- MkBind fc nm Explicit rig <$> quote (length env) ty
      getFields !(sc $$ VVar fc (length env) [<]) env (bnd :: bnds)
    getFields tm@(VPi fc nm _ rig ty sc) env bnds = getFields !(sc $$ VVar fc (length env) [<]) env bnds
    getFields tm xs bnds = pure $ reverse bnds

    tenv : Nat -> Env
    tenv Z = []
    tenv (S k) = (VVar emptyFC k [<] :: tenv k)

    mkRHS : String -> List Binder -> Raw -> Raw
    mkRHS instName (MkBind fc nm Explicit rig ty :: bs) tm = mkRHS instName bs (RApp fc tm (RVar fc "\{instName},\{nm}") Explicit)
    mkRHS instName (b :: bs) tm = mkRHS instName bs tm
    mkRHS instName [] tm = tm

    apply : Val -> List Val -> M Val
    apply x [] = pure x
    apply (VPi fc nm icit rig a b) (x :: xs) = apply !(b $$ x) xs
    apply x (y :: xs) = error instfc "expected pi type \{show x}"

processDecl (Data fc nm ty cons) = do
  putStrLn "-----"
  putStrLn "Data \{nm}"
  top <- get
  mc <- readIORef top.metas
  let mstart = length mc.metas
  tyty <- check (mkCtx fc) ty (VU fc)
  case lookup nm top of
    Just (MkEntry name type Axiom) => do
      unifyCatch fc (mkCtx fc) !(eval [] CBN tyty) !(eval [] CBN type)
    Just (MkEntry name type _) => error fc "\{show nm} already declared"
    Nothing => setDef nm fc tyty Axiom
  cnames <- for cons $ \x => case x of
      (TypeSig fc names tm) => do
          debug "check dcon \{show names} \{show tm}"
          dty <- check (mkCtx fc) tm (VU fc)
          debug "dty \{show names} is \{pprint [] dty}"

          -- We only check that codomain uses the right type constructor
          -- We know it's in U because it's part of a checked Pi type
          let (codomain, tele) = splitTele dty
          -- for printing
          let tnames = reverse $ map (\(MkBind _ nm _ _ _) => nm) tele
          let (Ref _ hn _, args) := funArgs codomain
            | (tm, _) => error (getFC tm) "expected \{nm} got \{pprint tnames tm}"
          when (hn /= nm) $
            error (getFC codomain) "Constructor codomain is \{pprint tnames codomain} rather than \{nm}"

          for_ names $ \ nm' => do
            setDef nm' fc dty (DCon (getArity dty) nm)
          pure names
      decl => throwError $ E (getFC decl) "expected constructor declaration"
  putStrLn "setDef \{nm}  TCon \{show $ join cnames}"
  updateDef nm fc tyty (TCon (join cnames))
  -- logMetas mstart
  where
    checkDeclType : Tm -> M ()
    checkDeclType (U _) = pure ()
    checkDeclType (Pi _ str icit rig t u) = checkDeclType u
    checkDeclType _ = error fc "data type doesn't return U"
