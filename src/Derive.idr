module Derive

import public Language.Reflection
-- import public Language.Elab.Syntax
-- import public Language.Elab.Types

-- Is base not in scope?
-- import public Deriving.Common

%language ElabReflection

getType1 : Name -> Elab (Name,TTImp)
getType1 name = do
  [rval] <- getType name 
    | [] => fail "can't get fullname for \{show name}"
    | _  => fail "ambiguous name \{show name}"
  pure rval


fullName : Name -> Elab Name
fullName name = do
  [(qname,_)] <- getType name 
    | [] => fail "can't get fullname for \{show name}"
    | _  => fail "ambiguous name \{show name}"
  pure qname

export
deriveShow : Name -> Elab ()
deriveShow name = do
    myGoal <- goal
    logMsg "foo" 1 $ "my goal is \{show myGoal}"
    fname <- fullName name
    logMsg "foo" 1 $ "woo \{show fname}"
    cons <- getCons fname
    logMsg "foo" 1 $ "cons \{show cons}"
    for_ cons $ \name => do
      logMsg "foo" 1 $ "getType1 \{show name}"
      (_,type) <- getType1 name
      logTerm "foo" 1 (show name) type
      -- type doesn't really matter, we need the explicit arity and the base name
      


    pure ()


