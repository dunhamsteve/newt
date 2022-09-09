module Lib.Layout

import Lib.Token
import Text.Lexer

-- Dunno if I'll do layout or pass col, but here it is:

intro : List String
intro = [ "where", "let", "of" ]

Position : Type
Position = (Int,Int)

isIntro : BTok -> Bool
isIntro t = elem (value t) intro

export
layout : List BTok -> List BTok
layout = go [] []
  where
    lbrace = irrelevantBounds (Tok LBrace "{")
    semi = irrelevantBounds (Tok Semi ";")
    rbrace = irrelevantBounds (Tok RBrace "}")

    -- go' does start of block
    go' : List BTok -> List Position -> List BTok -> List BTok

    -- go does semi and end of block, we require "in" to be on separate, outdented line if not the same line as let
    go : List BTok -> List Position -> List BTok -> List BTok
    go acc lvls [] = reverse acc
    go acc [] ts = go' acc [] ts
    go acc lvls@(lvl::rest) toks@(t :: ts) =
      let (sr,sc) = start t in
      if      snd lvl >  sc then go (rbrace :: acc) rest toks
      else if snd lvl == sc then go' (semi :: acc) lvls toks
      else if value t == "in" && sr == fst lvl then go' (rbrace :: acc) rest toks
      else go' acc lvls toks
    
    -- handle start of block
    go' acc lvls [] = reverse acc
    go' acc lvls (t::ts) = case isIntro t of
      False => go (t::acc) lvls ts
      True => case ts of
          t'::ts' => go (t' :: lbrace :: t :: acc) (start t' :: lvls) ts'
          []      => go (rbrace :: lbrace :: t :: acc) lvls ts

      
      