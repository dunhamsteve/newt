module Lib.Parser


import Lib.Token
import Lib.Parser.Impl
import Syntax

-- There is the whole core vs surface thing here.
-- might be best to do core first/ Technically don't
-- _need_ a parser, but would be useful for testing.

-- look to pi-forall / ezoo, but I think we start with a
-- TTImpl level grammar, then add a more sugared layer above
-- so holes and all that

-- After the parser runs, see below, take a break and finish pi-forall
-- exercises.  There is some fill in the parser stuff that may show 
-- the future.

ident = token Ident

term : Parser Term

letExpr : Parser Term
letExpr = Let <$ keyword "let" <*> ident <* keyword "=" <*> term <* keyword "in" <*> term

pattern : Parser Pattern

lamExpr : Parser Term
lamExpr = do
  keyword "\\"
  commit
  name <- pattern
  keyword "."
  scope <- term
  pure $ Lam name scope

caseAlt : Parser CaseAlt

caseExpr : Parser Term
caseExpr = do
  _ <- keyword "case"
  commit
  sc <- term
  keyword "of"
  alts <- startBlock $ someSame $ caseAlt
  pure $ Case sc alts



-- TODO - get this up and running with a case expr to test it



{-
so lets say we wanted to do the indent, the hard way. 

what does this look like

We want to say:
   kw 'let' $  indentedSome assignment

now assignment is going to be whatever, but we need to make sure the initial token can/must be at
current indentation level.

Ok idris indent is not Col, it's AnyIndent | AtPos Int | AfterPos Int

The col though is somehow sixty.

sixten is sameCol, dropAnchor, with an "environment"


sixty is Position is line and col and either line matches or col < tokenCol.

that's maybe doable..




 -}

