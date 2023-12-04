module Text.Lexing.Tokeniser

import Data.Location
import Data.Util

import Text.Bounded
import Text.Lexing.Token

accountFor : Char -> (Bool, Int -> Int, Int -> Int)
accountFor x = (isNL x || isSpace x, ifThenElse (isNL x) ((+ 1), const 0) (id, (+ 1)))

mkBounds : (Int, Int) -> (Int, Int) -> Bounds
mkBounds (startL, startC) (endL, endC) = MkBounds startL startC endL endC

apply2 : (a -> b, a' -> b') -> (a, a') -> (b, b')
apply2 (f, g) (x, y) = (f x, g y)

compose2 : (b -> c, b' -> c') -> (a -> b, a' -> b') -> (a -> c, a' -> c')
compose2 (g, g') (f, f') = (g . f, g' . f')

public export
data State = InSinglelineComment | InMultilineComment | AccWhitespace | Normal

||| Recusion principle for State.
state : a -> a -> a -> a -> State -> a
state inSinglelineComment inMultilineComment accWhitespace normal InSinglelineComment = inSinglelineComment
state inSinglelineComment inMultilineComment accWhitespace normal InMultilineComment = inMultilineComment
state inSinglelineComment inMultilineComment accWhitespace normal AccWhitespace = accWhitespace
state inSinglelineComment inMultilineComment accWhitespace normal Normal = normal

||| Populates bounds information.
||| Combines consecutive whitespace symbols into one token.
||| Combines single-line comments into one token.
export
mkWithBounds : (accW : State)
            -> state ((Int, Int), (Int -> Int, Int -> Int), SnocList Char)
                     ((Int, Int), (Int -> Int, Int -> Int), SnocList Char)
                     ((Int, Int), (Int -> Int, Int -> Int))
                     (Int, Int)
                     accW
            -> List Char
            -> List (WithBounds Token)
mkWithBounds InSinglelineComment (p, delta, comment) [] =
  let p' = delta `apply2` p in
  [MkBounded (Comment comment) False (mkBounds p p')]
mkWithBounds InMultilineComment (p, delta, comment) [] =
  let p' = delta `apply2` p in
  [MkBounded (Comment comment) False (mkBounds p p')]
-- Remove the trailing whitespace
mkWithBounds AccWhitespace (p, delta) [] = []
mkWithBounds Normal _ [] = []
mkWithBounds Normal p ('-' :: '-' :: xs) =
  mkWithBounds InSinglelineComment (p, (id, (+ 2)), [<]) xs
mkWithBounds Normal p ('{' :: '-' :: xs) =
  mkWithBounds InMultilineComment (p, (id, (+ 2)), [<]) xs
mkWithBounds AccWhitespace (p, delta) ('-' :: '-' :: xs) =
  let p' = delta `apply2` p in
  let w = MkBounded Whitespace False (mkBounds p p') in
  w :: mkWithBounds InSinglelineComment (p', (id, (+ 2)), [<]) xs
mkWithBounds AccWhitespace (p, delta) ('{' :: '-' :: xs) =
  let p' = delta `apply2` p in
  let w = MkBounded Whitespace False (mkBounds p p') in
  w :: mkWithBounds InMultilineComment (p', (id, (+ 2)), [<]) xs
mkWithBounds Normal p (x :: xs) =
  let (isW, delta) = accountFor x in
  case isW of
    False =>
      let p' = delta `apply2` p in
      MkBounded (Symbol x) False (mkBounds p p') :: mkWithBounds Normal p' xs
    True => mkWithBounds AccWhitespace (p, delta) xs
mkWithBounds AccWhitespace (p, delta) (x :: xs) =
  let (isW, delta') = accountFor x in
  case isW of
    False =>
      let p' = delta `apply2` p in
      let p'' = (delta' `compose2` delta) `apply2` p in
      MkBounded Whitespace False (mkBounds p p') :: MkBounded (Symbol x) False (mkBounds p' p'') :: mkWithBounds Normal p'' xs
    True => mkWithBounds AccWhitespace (p, delta' `compose2` delta) xs
    -- This will fail on windows                  vvvv
mkWithBounds InSinglelineComment (p, delta, str) ('\n' :: xs) =
  let p' = delta `apply2` p in
  let comment = MkBounded (Comment str) False (mkBounds p p') in
  let p'' = ((+ 1), const 0) `apply2` p' in
  comment :: mkWithBounds Normal p'' xs
    -- BUG:
    -- This will fail on windows (and not only?) vvvv
mkWithBounds InMultilineComment (p, delta, str) ('\n' :: xs) =
  -- As soon as we hit a new line,
  -- we ship a comment token and continue
  -- we do this to keep us to single-line semantic tokens only.
  let p' = delta `apply2` p in
  let comment = MkBounded (Comment str) False (mkBounds p p') in
  let p'' = ((+ 1), const 0) `apply2` p' in
  comment :: mkWithBounds InMultilineComment (p'', (id, id), str) xs
mkWithBounds InMultilineComment (p, delta, str) ('-' :: '}' :: xs) =
  let p' = ((id, (+ 2)) `compose2` delta) `apply2` p in
  let comment = MkBounded (Comment str) False (mkBounds p p') in
  comment :: mkWithBounds Normal p' xs
mkWithBounds InSinglelineComment (p, delta, str) (x :: xs) =
  mkWithBounds InSinglelineComment (p, (id, (+ 1)) `compose2` delta, str :< x) xs
mkWithBounds InMultilineComment (p, delta, str) (x :: xs) =
  mkWithBounds InMultilineComment (p, (id, (+ 1)) `compose2` delta, str :< x) xs

export
filterOutComments : List (WithBounds Token) -> (SnocList Range, List (WithBounds Token))
filterOutComments [] = ([<], [])
filterOutComments (MkBounded (Comment _) _ range :: xs) =
  mapFst (:< (cast range)) (filterOutComments xs)
filterOutComments (x :: xs) =
  mapSnd (x ::) (filterOutComments xs)

min2 : (Int, Int) -> (Int, Int) -> (Int, Int)
min2 (l, c) (l', c') =
  ifThenElse (l < l') (l, c) $
    ifThenElse (l == l') (ifThenElse (c < c') (l, c) (l', c')) $
      (l', c')

max2 : (Int, Int) -> (Int, Int) -> (Int, Int)
max2 (l, c) (l', c') =
  ifThenElse (l < l') (l', c') $
    ifThenElse (l == l') (ifThenElse (c < c') (l', c') (l, c)) $
      (l, c)

||| (s, e) ∪ (s', e') =
||| (min (s, s'), max (e, e'))
export
union : Bounds -> Bounds -> Bounds
union (MkBounds sl sc el ec) (MkBounds sl' sc' el' ec') =
  let (minl, minc) = min2 (sl, sc) (sl', sc') in
  let (maxl, maxc) = max2 (el, ec) (el', ec') in
  MkBounds minl minc maxl maxc

export
mergeWhitespace : List (WithBounds Token) -> List (WithBounds Token)
mergeWhitespace [] = []
mergeWhitespace (MkBounded Whitespace r p :: MkBounded Whitespace r' p' :: xs) =
  mergeWhitespace (MkBounded Whitespace (r || r') (union p p') :: xs)
mergeWhitespace (x :: xs) = x :: mergeWhitespace xs

export
removeLeadingWhitespace : List (WithBounds Token) -> List (WithBounds Token)
removeLeadingWhitespace [] = []
removeLeadingWhitespace (MkBounded Whitespace {} :: xs) =
  removeLeadingWhitespace xs
removeLeadingWhitespace (x :: xs) = x :: xs

export
removeTrailingWhitespace : List (WithBounds Token) -> List (WithBounds Token)
removeTrailingWhitespace [] = []
removeTrailingWhitespace [MkBounded Whitespace {}] = []
removeTrailingWhitespace (x :: xs) = x :: removeTrailingWhitespace xs

namespace Show.Token
  public export
  [BriefInst] Show Token where
    show (Symbol x) = cast x
    show Whitespace = " "
    show (Comment str) = "/"

  public export
  [WithBoundsBriefInst] Show (WithBounds Token) where
    show (MkBounded tok isIrr (MkBounds l c l' c')) =
      show @{BriefInst} tok ++ "(\{show l}:\{show c}-\{show l'}:\{show c'})"

  public export
  [WithBoundsBriefListInst] Show (List (WithBounds Token)) where
    show xs = show @{NLSepList @{WithBoundsBriefInst}} xs

export
tokenise : List Char -> (SnocList Range, List (WithBounds Token))
tokenise = mapSnd removeLeadingWhitespace
         . mapSnd removeTrailingWhitespace
         . mapSnd mergeWhitespace
         . filterOutComments --vvvvvv We count starting at 0 for both axes,
         . mkWithBounds Normal (0, 0) -- solely because LSP expects this format.
