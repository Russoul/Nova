module Control.Monad.FailSt

import Data.List
import Data.List1
import Data.SnocList
import Data.Vect
import Data.AVL

import System.File.ReadWrite

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import public System.Clock

%inline
public export
Arrow : Type -> Type -> Type
Arrow a b = a -> b

public export
data Channel = Timing | Debug

public export
Show Channel where
  show Timing = "Timing"
  show Debug = "Debug"

public export
Eq Channel where
  Timing  == Timing  = True
  Debug   == Debug   = True
  _       == _       = False

%inline
public export
Subset : Type -> Type
Subset a = a -> Bool

||| Failure over stateful computation with filtered eager fail-resistant debug output.
%inline
public export
FailStM : (err : Type) -> (st : Type) -> (res : Type) -> Type
FailStM e s = Arrow (Subset Channel, s) . IO . (Subset Channel,) . Either e . (s, )

namespace FailSt
  %inline
  public export
  (>>=) : FailStM e s a -> (a -> FailStM e s b) -> FailStM e s b
  m >>= f = \s => Prelude.do
    case !(m s) of
      (ch, Left e) => pure (ch, Left e)
      (ch, Right (s, x)) => f x (ch, s)

  %inline
  public export
  (=<<) : (a -> FailStM e s b) -> FailStM e s a -> FailStM e s b
  (=<<) = flip (>>=)

  %inline
  public export
  (>=>) : (a -> FailStM e s b) -> (b -> FailStM e s c) -> (a -> FailStM e s c)
  (>=>) f g x = g !(f x)


  %inline
  public export
  (<=<) : (b -> FailStM e s c) -> (a -> FailStM e s b) -> (a -> FailStM e s c)
  (<=<) = flip (>=>)

  %inline
  public export
  (>>) : FailStM e s () -> FailStM e s b -> FailStM e s b
  (>>) m f = (>>=) m (const f)

  %inline
  public export
  return : a -> FailStM e s a
  return x = \(ch, s) => pure (ch, Right (s, x))

  %inline
  public export
  throw : e -> FailStM e s a
  throw e (ch, s) = pure (ch, Left e)

  %inline
  public export
  get : FailStM e s s
  get = \(ch, s) => pure (ch, Right (s, s))

  %inline
  public export
  set : s -> FailStM e s ()
  set s (ch, _) = pure (ch, Right (s, ()))

  %inline
  public export
  update : (s -> s) -> FailStM e s ()
  update f = get >>= set . f

  public export
  mapError : (e -> e') -> FailStM e s a -> FailStM e' s a
  mapError f m = \s => Prelude.do
    case !(m s) of
      (ch, Left x) => pure (ch, Left (f x))
      (ch, Right x) => pure (ch, Right x)

  public export
  mapState : (s -> s') -> (s' -> s) -> FailStM e s a -> FailStM e s' a
  mapState f f' m = \(ch, s') => Prelude.do
    case !(m (ch, f' s')) of
      (ch, Left x) => pure (ch, Left x)
      (ch, Right (st, x)) => pure (ch, Right (f st, x))

  public export
  mapResult : (a -> b) -> FailStM e s a -> FailStM e s b
  mapResult f m = \s => Prelude.do
    case !(m s) of
      (ch, Left x) => pure (ch, Left x)
      (ch, Right (st, x)) => pure (ch, Right (st, f x))

  public export
  (<$>) : (a -> b) -> FailStM e s a -> FailStM e s b
  (<$>) = mapResult

  public export
  (<&>) : FailStM e s a -> (a -> b) -> FailStM e s b
  (<&>) = flip mapResult

  public export
  (<*>) : FailStM e s (a -> b) -> FailStM e s a -> FailStM e s b
  (<*>) f x = FailSt.do
    f <- f
    x <- x
    return (f x)

  public export
  fromEither : Either e a -> FailStM e s a
  fromEither (Left x) (ch, s) = pure (ch, Left x)
  fromEither (Right x) (ch, s) = pure (ch, Right (s, x))

  ||| Runs gathering output from all channels.
  public export
  run : FailStM e s r -> s -> IO (Either e (s, r))
  run m initial = map snd (m (const True, initial))

  ||| Runs gathering output from all channels.
  public export
  eval : FailStM e s r -> s -> IO (Either e r)
  eval m initial = Prelude.do
    case !(m (const True, initial)) of
      (ch, Left x) => pure (Left x)
      (ch, Right (st, x)) => pure (Right x)

  public export
  discard : FailStM e s a -> FailStM e s ()
  discard x = x >>= const (return ())

  public export
  when : Bool -> FailStM e s () -> FailStM e s ()
  when True x = x
  when False x = return ()

  public export
  listeningOn : Channel -> FailStM e s Bool
  listeningOn me = \(listen, s) => pure (listen, (Right (s, listen me)))

  {- public export
  write : g -> FailStM' g e s ()
  write gl = \s => pure (gl, Right (s, ())) -}

  public export
  forList : List a -> (a -> FailStM e s b) -> FailStM e s (List b)
  forList [] f = return []
  forList (x :: xs) f = do
    y <- f x
    ys <- forList xs f
    return (y :: ys)

  public export
  forPair : (a, b)
         -> (a -> FailStM e s a')
         -> (b -> FailStM e s b')
         -> FailStM e s (a', b')
  forPair (x, y) f g = return (!(f x), !(g y))

  public export
  traversePair : (a -> FailStM e s a')
              -> (b -> FailStM e s b')
              -> (a, b)
              -> FailStM e s (a', b')
  traversePair f g (x, y) = return (!(f x), !(g y))

  public export
  traverseOrdTree : {o, o' : _}
                 -> (a -> FailStM e s b)
                 -> OrdTree a o -> FailStM e s (OrdTree b o')
  traverseOrdTree f tree = FailSt.do
    foldl (\tree, x => FailSt.do return $ insert !(f x) !tree) (return empty) tree

  public export
  forCatMaybes : List a
              -> (a -> FailStM e s (Maybe b))
              -> FailStM e s (List b)
  forCatMaybes list f =
    mapResult catMaybes (forList list f)

  public export
  forList1 : List1 a -> (a -> FailStM e s b) -> FailStM e s (List1 b)
  forList1 (x ::: xs) f = FailSt.do
     x <- f x
     xs <- forList xs f
     return (x ::: xs)

  public export
  forSnocList : SnocList a -> (a -> FailStM e s b) -> FailStM e s (SnocList b)
  forSnocList [<] f = return [<]
  forSnocList (xs :< x) f = do
    y <- f x
    ys <- forSnocList xs f
    return (ys :< y)

  public export
  traverseSnocList : (a -> FailStM e s b)
                  -> SnocList a
                  -> FailStM e s (SnocList b)
  traverseSnocList f xs = forSnocList xs f

  public export
  traverseList : (a -> FailStM e s b)
              -> List a
              -> FailStM e s (List b)
  traverseList f xs = forList xs f

  public export
  traverseList1 : (a -> FailStM e s b)
               -> List1 a
               -> FailStM e s (List1 b)
  traverseList1 f xs = forList1 xs f

  public export
  traverseList_ : (a -> FailStM e s ())
               -> List a
               -> FailStM e s ()
  traverseList_ f xs = discard $ traverseList f xs

  public export
  traverseList1_ : (a -> FailStM e s ())
                -> List1 a
                -> FailStM e s ()
  traverseList1_ f xs = discard $ traverseList1 f xs

  public export
  forVect : Vect n a -> (a -> FailStM e s b) -> FailStM e s (Vect n b)
  forVect [] f = return []
  forVect (x :: xs) f = do
    y <- f x
    ys <- forVect xs f
    return (y :: ys)

  public export
  forMaybe : Maybe a -> (a -> FailStM e s b) -> FailStM e s (Maybe b)
  forMaybe Nothing f = return Nothing
  forMaybe (Just x) f = do
    r <- f x
    return (Just r)

  public export
  traverseMaybe : (a -> FailStM e s b)
               -> Maybe a
               -> FailStM e s (Maybe b)
  traverseMaybe f m = forMaybe m f

  public export
  forList_ : List a -> (a -> FailStM e s b) -> FailStM e s ()
  forList_ xs f = discard $ forList xs f

  public export
  forSnocList_ : SnocList a -> (a -> FailStM e s b) -> FailStM e s ()
  forSnocList_ xs f = discard $ forSnocList xs f

  public export
  forVect_ : Vect n a -> (a -> FailStM e s b) -> FailStM e s ()
  forVect_ xs f = discard $ forVect xs f

  public export
  filterMaybeListM : List a -> (a -> FailStM e s (Maybe b)) -> FailStM e s (List b)
  filterMaybeListM [] f = return []
  filterMaybeListM (x :: xs) f = FailSt.do
    rest <- filterMaybeListM xs f
    r <- f x
    case r of
      Nothing => return rest
      Just x' => return (x' :: rest)

  public export
  pushInMaybe : Maybe (FailStM e s a) -> FailStM e s (Maybe a)
  pushInMaybe Nothing = return Nothing
  pushInMaybe (Just x) = return (Just !x)

  public export
  pushInList : List (FailStM e s a)
            -> FailStM e s (List a)
  pushInList [] = return []
  pushInList (x :: xs) = return (!x :: !(pushInList xs))

  public export
  pushInProduct : (FailStM e s a, FailStM e s b)
               -> FailStM e s (a, b)
  pushInProduct (f, g) = return (!f, !g)

  public export
  pushInEither : Either (FailStM e s a) (FailStM e s b)
              -> FailStM e s (Either a b)
  pushInEither (Left f)  = return (Left !f)
  pushInEither (Right g) = return (Right !g)

  ||| Never fails.
  public export
  try : FailStM e s a -> FailStM e s (Either e a)
  try m = \(ch, s) => Prelude.do
    case !(m (ch, s)) of
      (ch, Left x) => pure (ch, Right (s, Left x))
      (ch, Right (s, x)) => pure (ch, Right (s, Right x))

  ||| First working alternative.
  public export
  (<|>) : FailStM e s a -> FailStM e s a -> FailStM e s a
  (f <|> g) = FailSt.do
    case !(try f) of
      Left err => g
      Right ok => return ok

  public export
  allList : List (FailStM e s Bool) -> FailStM e s Bool
  allList [] = return True
  allList (x :: xs) = FailSt.do
    x <- x
    case x of
      False => return False
      True => allList xs

  ||| Lazy logical disjunction.
  public export
  or : FailStM e s Bool -> FailStM e s Bool -> FailStM e s Bool
  or a b = FailSt.do
    case !a of
      True => return True
      False => b

  infixr 8 `and`

  infixr 7 `or`

  ||| Lazy logical disjunction.
  public export
  and : FailStM e s Bool -> FailStM e s Bool -> FailStM e s Bool
  and a b = FailSt.do
    case !a of
      True => b
      False => return False

  public export
  io : IO a -> FailStM e s a
  io cmd (ch, s) = Prelude.do
    r <- cmd
    pure (ch, Right (s, r))

  DEBUG_FILE = "debug.txt"

  data DebugOutput = STDOUT | FILE

  DEBUG_OUTPUT = STDOUT

  ||| Eagerly prints something out (using IO) on the given channel.
  public export
  print_ : Channel -> String -> FailStM e s ()
  print_ ch str = FailSt.do
    when !(listeningOn ch) $ FailSt.do
      case DEBUG_OUTPUT of
        STDOUT => io $ putStrLn str
        FILE => discard $ io $ appendFile {io = IO} DEBUG_FILE str

  public export
  timestamp : FailStM e s (Clock Process)
  timestamp = io $ clockTime Process

  public export
  gcTimestamp : FromString e => FailStM e s (Clock GCCPU)
  gcTimestamp = FailSt.do
    Just x <- io $ clockTime GCCPU
      | _ => throw ("GC CPU-time not supported")
    return x

  ||| NOTE: Division by 1M is *very* slow!
  ||| Like it takes a few seconds slow!
  public export
  showMillis : Clock type -> String
  showMillis (MkClock s ns) =
    let ms = ns `div` 1000000 in
    show s ++ "s " ++ show ms ++ "ms"

  -- Whole seconds & 3 significant fractional digits
  public export
  formatted : Clock type -> String
  formatted (MkClock sec nan) =
    let mantisa = cast {to = Int} (cast {to = Double} nan / 1_000_000) in -- XXX.GARBAGE
    "\{show sec}.\{pad mantisa}s"
   where
    pad : Int -> String
    pad x =
      case x < 10 of
        True => "00" ++ show x
        False =>
          case x < 100 of
            True => "0" ++ show x
            False => show x

  ||| Clocks the given computation, prints out (eagerly) the time it took to run the computation.
  public export
  clock : FromString e => String -> FailStM e s a -> FailStM e s a
  clock msg m = FailSt.do
    t0 <- timestamp
    t0' <- gcTimestamp
    r <- m
    t1 <- timestamp
    t1' <- gcTimestamp
    let dif = timeDifference t1 t0
    let dif' = timeDifference t1' t0'
    print_ Timing "\{msg} took overall-time: \{formatted dif}; gc time: \{formatted dif'}"
    return r

  ||| Clocks the given computation when the condition is true, prints out (eagerly) the time it took to run the computation.
  public export
  clockWhen : FromString e => Bool -> String -> FailStM e s a -> FailStM e s a
  clockWhen False msg m = m
  clockWhen True msg m = clock msg m

  public export
  clockThresholdD : FromString e => (a -> FailStM e s String) -> Integer -> FailStM e s a -> FailStM e s a
  clockThresholdD msg threshold m = FailSt.do
    t0 <- timestamp
    t0' <- gcTimestamp
    r <- m
    t1 <- timestamp
    t1' <- gcTimestamp
    let dif = timeDifference t1 t0
    let dif' = timeDifference t1' t0'
    let workloadTime = toNano dif - toNano dif'
    -- It has been noticed that sometimes trivial operations are claimed to take insensible amount of time.
    -- Coincidence or not, such claims have been always accompanied by 0 nanosecond GC time.
    -- By filtering out all output that has zero GC time, we discard spurious output.
    -- That means some output is lost (never shown) but the trade-off has been worth it so far.
    when (workloadTime > threshold && toNano dif' > 0) $ FailSt.do
      msg <- msg r
      print_ Timing "\{msg} took overall-time: \{formatted dif}; gc time: \{formatted dif'}" -- ; workload time: \{show workloadTime}ns"
    return r

  ||| Clocks the given computation, prints out (eagerly) the time it took to run the computation.
  public export
  clockThreshold : FromString e => String -> Integer -> FailStM e s a -> FailStM e s a
  clockThreshold msg threshold m = FailSt.do
    clockThresholdD (\x => return msg) threshold m

  ||| Currently, write is just an alias to print_ on *Debug* channel.
  ||| So all output of write is eagerly shown in console.
  public export
  write : SnocList String -> FailStM e s ()
  write [<] = return ()
  write (xs :< x) = FailSt.do
    write xs
    print_ Debug x

  ||| Computes the workload time (process time - GC time)
  public export
  time : FromString e => FailStM e s a -> FailStM e s (a, Clock Duration)
  time computation = FailSt.do
   t0 <- timestamp
   t0' <- gcTimestamp
   x <- computation
   t1 <- timestamp
   t1' <- gcTimestamp
   let dif = timeDifference t1 t0
   let dif' = timeDifference t1' t0'
   let workloadTime = timeDifference dif dif'
   return (x, workloadTime)
