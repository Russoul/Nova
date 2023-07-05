module Data.Location

import Data.AVL
import Data.Maybe
import Data.SnocList
import Data.Util

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import Text.Bounded

-----------------------------------------------
-------------- Source location ----------------
-----------------------------------------------

||| Point in a symbolic two-dimentional array.
public export
Point : Type
Point = (Int, Int)

namespace Ord.Point
  ||| Total order over Point.
  ||| Order induced over the pair of first components
  |||  always outweighs the one induced over the pair of second components.
  public export
  [Inst] Ord Point where
    compare (l, c) (l', c') =
      case compare l l' of
        EQ => compare c c'
        r  => r

||| Location of some entity in a symbolic array.
||| Has start and end points.
public export
record Range where
  constructor MkRange
  start : Point
  end : Point

public export
Show Range where
  show (MkRange s e) = "[" ++ show s ++ ", " ++ show e ++ "]"

namespace Range
  public export
  Eq Range where
    (MkRange a b) == (MkRange a' b') = (a == a') && (b == b')

public export
Cast Bounds Range where
  cast (MkBounds startLine startCol endLine endCol) =
    MkRange (startLine, startCol) (endLine, endCol)

public export
Cast Range Bounds where
  cast (MkRange (startLine, startCol) (endLine, endCol)) =
    MkBounds startLine startCol endLine endCol

namespace Ord.Range
  ||| Total order over Range.
  ||| Order induced over the pair of first components
  |||  always outweighs the one induced over the pair of second components.
  public export
  [Inst] Ord Range where
    compare (MkRange l c) (MkRange l' c') =
      case compare @{Ord.Point.Inst} l l' of
        EQ => compare @{Ord.Point.Inst} c c'
        r  => r

||| This data-type expresses a stateful *symmetric* relation
||| between two geometric intervals.
||| Possible states are:
||| Out <=> intervals do not intersect
||| Over <=> one interval lies over the other (or vice versa)
||| In <=> one interval is within another (or vice versa)
public export
data SymmetricInterposition = Out | Over | In

public export
isIntersection : SymmetricInterposition -> Bool
isIntersection Out  = False
isIntersection Over = True
isIntersection In   = True

namespace Range
  public export
  setStart : Point -> Range -> Range
  setStart start (MkRange _ end) = MkRange start end

  public export
  setEnd : Range -> Point -> Range
  setEnd (MkRange start _) end = MkRange start end

  -- a' a b b'
  public export
  isWithin : (inner : Range) -> (outer : Range) -> Bool
  isWithin (MkRange a b) (MkRange a' b') = (a' <= a) @{Point.Inst} && (b <= b') @{Point.Inst}

  public export
  isPointWithinRange : (point : Point) -> (outer : Range) -> Bool
  isPointWithinRange p (MkRange a b) = (a <= p) @{Point.Inst} && (p <= b) @{Point.Inst}

  public export
  symmetricInterposition : (a : Range) -> (b : Range) -> SymmetricInterposition
  symmetricInterposition (MkRange a b) (MkRange a' b') =
    case compare @{Point.Inst} a a' of
      LT =>
        case compare @{Point.Inst} a' b of
          LT =>
            case compare @{Point.Inst} b b' of
              LT => Over
              _ => In
          _ => Out
      EQ => In
      GT =>
        case compare @{Point.Inst} a b' of
          LT =>
            case compare @{Point.Inst} b' b of
              LT => Over
              _ => In
          _ => Out

public export
FileName : Type
FileName = String

public export
Loc : Type
Loc = (Maybe FileName, Maybe Range)

%name Loc loc

namespace Range
  public export
  (+) : Range -> Range -> Range
  a + b = setEnd a b.end

namespace Loc
  public export
  (+) : Loc -> Loc -> Loc
  (mbf0, mbr0) + (mbf1, mbr1) =
   (
    (do f0 <- mbf0
        f1 <- mbf1
        Just f0)
   ,
    (do r0 <- mbr0
        r1 <- mbr1
        Just (setEnd r0 r1.end))
   )

  public export
  isWithin : Loc -> Loc -> Bool
  isWithin (Nothing, x) (Nothing, y) = fromMaybe False [| isWithin x y |]
  isWithin (Just _, _) (Nothing, _) = False
  isWithin (Nothing, _) (Just _, _) = False
  isWithin (Just f, x) (Just f', y) =
    (f == f') && fromMaybe False [| isWithin x y |]

  public export
  isPointWithinLoc : (point : (Maybe FileName, Point)) -> (outer : Loc) -> Bool
  isPointWithinLoc (Just _, _) (Nothing, _) = False
  isPointWithinLoc (Nothing, _) (Just _, _) = False
  isPointWithinLoc (Nothing, p) (Nothing, mbRange) = fromMaybe False (isPointWithinRange p <$> mbRange)
  isPointWithinLoc (Just f, p) (Just f', mbRange) =
    f == f' && fromMaybe False (isPointWithinRange p <$> mbRange)

  public export
  symmetricInterposition : Loc -> Loc -> SymmetricInterposition
  symmetricInterposition (Nothing, x) (Nothing, y) = fromMaybe Out [| symmetricInterposition x y |]
  symmetricInterposition (Just _, _) (Nothing, _) = Out
  symmetricInterposition (Nothing, _) (Just _, _) = Out
  symmetricInterposition (Just f, x) (Just f', y) =
    case f == f' of
      False => Out
      True => fromMaybe Out [| symmetricInterposition x y |]

  public export
  doIntersect : Loc -> Loc -> Bool
  doIntersect x y = isIntersection $ symmetricInterposition x y

namespace MbRange
  public export
  setStart : Point -> Maybe Range -> Maybe Range
  setStart l r = r <&> setStart l

  public export
  setEnd : Maybe Range -> Point -> Maybe Range
  setEnd l r = l <&> (\range => setEnd range r)

namespace Loc
  public export
  EmptyLoc : Loc
  EmptyLoc = (Nothing, Nothing)

namespace Show.MbFileName
  public export
  [Inst] Show (Maybe FileName) where
    show Nothing = "No filename"
    show (Just filename) = filename

namespace Show.MbRange
  public export
  [Inst] Show (Maybe Range) where
    show Nothing = "No location data"
    show (Just (MkRange (l, c) (l', c'))) =
      "(\{show l},\{show c}) -- (\{show l'}, \{show c'})"

namespace Show.Loc
  public export
  [Inst] Show Loc where
    show (mbfile, mbrange) =
         show @{MbFileName.Inst} mbfile
      ++ " : "
      ++ show @{MbRange.Inst} mbrange
