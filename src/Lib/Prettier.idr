||| A prettier printer, Philip Wadler
||| https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf
module Lib.Prettier

import Data.String
import Data.Nat

||| `Doc` is a pretty printing document.  Constructors are private, use
||| methods below.  `Alt` in particular has some invariants on it, see paper
||| for details. (Something along the lines of "the first line of left is not
||| bigger than the first line of the right".)
export
data Doc = Empty | Line | Text String | Nest Nat Doc | Seq Doc Doc | Alt Doc Doc

||| `DOC` is an intermediate form used during layout/rendering
data DOC = EMPTY | TEXT String DOC | LINE Nat DOC

flatten : Doc -> Doc
flatten Empty = Empty
flatten (Seq x y) = Seq (flatten x) (flatten y)
flatten (Nest i x) = flatten x
flatten Line = Text " "
flatten (Text str) = Text str
flatten (Alt x y) = flatten x

group : Doc -> Doc
group x = Alt (flatten x) x

layout : DOC -> String
layout EMPTY = ""
layout (LINE k x) = "\n" ++ replicate k ' ' ++ layout x
layout (TEXT str x) = str ++ layout x



||| Whether a documents first line fits.
fits : Nat -> DOC -> Bool
fits w x = if w < 0 then False else case x of
            EMPTY => True
            (LINE k x) => True
            (TEXT s x) => fits (w `minus` length s) x

better : Nat -> Nat -> DOC -> DOC -> DOC
better w k x y = if fits (w `minus` k) x then x else y

be : Nat -> Nat -> List (Nat, Doc) -> DOC
be w k [] = EMPTY
be w k ((i, Empty) :: xs) = be w k xs
be w k ((i, Line) :: xs) = LINE i (be w i xs)
be w k ((i, (Text s)) :: xs) = TEXT s (be w (k + length s) xs)
be w k ((i, (Nest j x)) :: xs) = be w k ((i+j,x)::xs)
be w k ((i, (Seq x y)) :: xs) = be w k ((i,x) :: (i,y) :: xs)
be w k ((i, (Alt x y)) :: xs) = better w k (be w k ((i,x)::xs))
                                           (be w k ((i,y)::xs))

best : Nat -> Nat -> Doc -> DOC
best w k x = be w k [(0,x)]

-- Public interface

export
pretty : Nat -> Doc -> String
pretty w x = layout (best w 0 x)

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
