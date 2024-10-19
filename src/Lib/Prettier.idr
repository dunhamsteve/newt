||| A prettier printer, Philip Wadler
||| https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf
module Lib.Prettier

import Data.String
import Data.Nat
import Data.Maybe

||| `Doc` is a pretty printing document.  Constructors are private, use
||| methods below.  `Alt` in particular has some invariants on it, see paper
||| for details. (Something along the lines of "the first line of left is not
||| bigger than the first line of the right".)
export
data Doc = Empty | Line | Text String | Nest Nat Doc | Seq Doc Doc | Alt Doc Doc

||| The original paper had a List-like structure Doc (the above was DOC) which
||| had Empty and a tail on Text and Line.
data Item = TEXT String | LINE Nat

export
empty : Doc
empty = Empty

flatten : Doc -> Doc
flatten Empty = Empty
flatten (Seq x y) = Seq (flatten x) (flatten y)
flatten (Nest i x) = flatten x
flatten Line = Text " "
flatten (Text str) = Text str
flatten (Alt x y) = flatten x

group : Doc -> Doc
group x = Alt (flatten x) x

-- TODO - we can accumulate snoc and cat all at once
layout : List Item -> String
layout [] = ""
layout (LINE k :: x) = "\n" ++ replicate k ' ' ++ layout x
layout (TEXT str :: x) = str ++ layout x

||| Whether a documents first line fits.
fits : Nat -> List Item -> Bool
fits 0 x = False
fits w ((TEXT s) :: xs) = fits (w `minus` length s) xs
fits w _ = True

-- vs Wadler, we're collecting the left side as a SnocList to prevent
-- blowing out the stack on the Text case.  The original had DOC as
-- a Linked-List like structure (now List Item)

-- I've now added a `fit` boolean to indicate if we should cut when we hit the line length
-- Wadler was relying on laziness to stop the first branch before LINE if necessary
be : Bool -> SnocList Item -> Nat -> Nat -> List (Nat, Doc) -> Maybe (List Item)
be fit acc w k [] = Just (acc <>> [])
be fit acc w k ((i, Empty) :: xs) = be fit acc w k xs
be fit acc w k ((i, Line) :: xs) = (be False (acc :< LINE i) w i xs)
be fit acc w k ((i, (Text s)) :: xs) =
  if not fit || (k + length s < w) 
     then (be fit (acc :< TEXT s) w (k + length s) xs) 
     else Nothing
be fit acc w k ((i, (Nest j x)) :: xs) = be fit acc w k ((i+j,x)::xs)
be fit acc w k ((i, (Seq x y)) :: xs) = be fit acc w k ((i,x) :: (i,y) :: xs)
be fit acc w k ((i, (Alt x y)) :: xs) =
  (acc <>>) <$> (be True [<] w k ((i,x)::xs) <|> be fit [<] w k ((i,y)::xs))

best : Nat -> Nat -> Doc -> List Item
best w k x = fromMaybe [] $ be False [<] w k [(0,x)]

-- Public interface
public export
interface Pretty a where
  pretty : a -> Doc

export
render : Nat -> Doc -> String
render w x = layout (best w 0 x)

public export
Semigroup Doc where x <+> y = Seq x (Seq (Text " ") y)

-- Match System.File so we don't get warnings
public export
infixl 5 </>

export
line : Doc
line = Line

export
text : String -> Doc
text = Text

export
nest : Nat -> Doc -> Doc
nest = Nest

export
(++) : Doc -> Doc -> Doc
x ++ y = Seq x y

export
(</>) : Doc -> Doc -> Doc
x </> y = x ++ line ++ y

||| fold, but doesn't emit extra nil
export
folddoc : (Doc -> Doc -> Doc) -> List Doc -> Doc
folddoc f [] = Empty
folddoc f [x] = x
folddoc f (x :: xs) = f x (folddoc f xs)

||| separate with space
export
spread : List Doc -> Doc
spread = folddoc (<+>)

||| separate with new lines
export
stack : List Doc -> Doc
stack = folddoc (</>)

||| bracket x with l and r, indenting contents on new line
export
bracket : String -> Doc -> String -> Doc
bracket l x r = group (text l ++ nest 2 (line ++ x) ++ line ++ text r)

infixl 5 <+/>

||| Either space or newline
export
(<+/>) : Doc -> Doc -> Doc
x <+/> y = x ++ (text " " `Alt` line) ++ y

||| Reformat some docs to fill. Not sure if I want this precise behavior or not.
export
fill : List Doc -> Doc
fill [] = Empty
fill [x] = x
fill (x :: y :: xs) = (flatten x <+> fill (flatten y :: xs)) `Alt` (x </> fill (y :: xs))

public export
FromString Doc where
  fromString = text
