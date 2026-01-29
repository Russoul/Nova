module Control.Monad.JustAMonad


import Data.List
import Data.List1
import Data.SnocList
import Data.Vect
import Data.Either

import Deriving.Show

import Language.Reflection

import System.File.ReadWrite

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import public System.Clock

%language ElabReflection

%inline
public export
Arrow : Type -> Type -> Type
Arrow a b = a -> b

public export
data Channel = Timing | Debug

%hint
export
channelShow : Show Channel
channelShow = %runElab derive

public export
Eq Channel where
  Timing  == Timing  = True
  Debug   == Debug   = True
  _       == _       = False

%inline
public export
Subset : Type -> Type
Subset a = a -> Bool

||| Failure over stateful computation wrapped in IO.
%inline
public export
M : (err : Type) -> (st : Type) -> (res : Type) -> Type
M e s = Arrow (Subset Channel, s) . IO . (Subset Channel,) . Either e . (s,)

namespace M
  ||| Chain computations. Main ingredient for overloaded do-notation.
  %inline
  public export
  (>>=) : M e s a -> (a -> M e s b) -> M e s b
  m >>= f = \s => Prelude.do
    case !(m s) of
      (ch, Left e) => pure (ch, Left e)
      (ch, Right (s, x)) => f x (ch, s)

  %inline
  public export
  (=<<) : (a -> M e s b) -> M e s a -> M e s b
  (=<<) = flip (>>=)

  ||| Composition of monadic functions.
  %inline
  public export
  (>=>) : (a -> M e s b) -> (b -> M e s c) -> (a -> M e s c)
  (>=>) f g x = g !(f x)

  %inline
  public export
  (<=<) : (b -> M e s c) -> (a -> M e s b) -> (a -> M e s c)
  (<=<) = flip (>=>)

  %inline
  public export
  (>>) : M e s () -> M e s b -> M e s b
  (>>) m f = (>>=) m (const f)

  ||| Wrap a pure result in a computation/monad.
  %inline
  public export
  return : a -> M e s a
  return x = \(ch, s) => pure (ch, Right (s, x))

  ||| Throw an error.
  %inline
  public export
  throw : e -> M e s a
  throw e (ch, s) = pure (ch, Left e)

  ||| Get the state.
  %inline
  public export
  get : M e s s
  get = \(ch, s) => pure (ch, Right (s, s))

  ||| Set the state.
  %inline
  public export
  set : s -> M e s ()
  set s (ch, _) = pure (ch, Right (s, ()))

  ||| Update the state.
  %inline
  public export
  update : (s -> s) -> M e s ()
  update f = get >>= set . f

  public export
  mapError : (e -> e') -> M e s a -> M e' s a
  mapError f m = \s => Prelude.do
    case !(m s) of
      (ch, Left x) => pure (ch, Left (f x))
      (ch, Right x) => pure (ch, Right x)

  public export
  mapState : (s -> s') -> (s' -> s) -> M e s a -> M e s' a
  mapState f f' m = \(ch, s') => Prelude.do
    case !(m (ch, f' s')) of
      (ch, Left x) => pure (ch, Left x)
      (ch, Right (st, x)) => pure (ch, Right (f st, x))

  public export
  mapResult : (a -> b) -> M e s a -> M e s b
  mapResult f m = \s => Prelude.do
    case !(m s) of
      (ch, Left x) => pure (ch, Left x)
      (ch, Right (st, x)) => pure (ch, Right (st, f x))

  public export
  (<$>) : (a -> b) -> M e s a -> M e s b
  (<$>) = mapResult

  public export
  (<&>) : M e s a -> (a -> b) -> M e s b
  (<&>) = flip mapResult

  public export
  (<*>) : M e s (a -> b) -> M e s a -> M e s b
  (<*>) f x = M.do
    f <- f
    x <- x
    return (f x)

  public export
  fromEither : Either e a -> M e s a
  fromEither (Left x) (ch, s) = pure (ch, Left x)
  fromEither (Right x) (ch, s) = pure (ch, Right (s, x))

  ||| Runs gathering output from all channels.
  public export
  run : M e s r -> s -> IO (Either e (s, r))
  run m initial = map snd (m (const True, initial))

  ||| Runs gathering output from all channels, throws away the resulting state.
  public export
  eval : M e s r -> s -> IO (Either e r)
  eval m initial = Prelude.do
    case !(m (const True, initial)) of
      (ch, Left x) => pure (Left x)
      (ch, Right (st, x)) => pure (Right x)

  ||| Run the computation and discard its result.
  public export
  discard : M e s a -> M e s ()
  discard x = x >>= const (return ())

  ||| Run the computation when the condition is true.
  public export
  when : Bool -> M e s () -> M e s ()
  when True x = x
  when False x = return ()

  ||| Check if the channel is listened.
  public export
  isListening : Channel -> M e s Bool
  isListening me = \(listen, s) => pure (listen, (Right (s, listen me)))

  ||| Sets whether to listen or not on that channel.
  public export
  doListen : Channel -> Bool -> M e s ()
  doListen ch switch = \(listen, s) => pure (set listen ch switch, Right (s, ()))
   where
    set : (Channel -> Bool) -> Channel -> Bool -> Channel -> Bool
    set f x switch y =
      case x == y of
       True => switch
       False => f x

  public export
  sequenceMaybe : Maybe (M e s a) -> M e s (Maybe a)
  sequenceMaybe Nothing = return Nothing
  sequenceMaybe (Just x) = return (Just !x)

  public export
  sequenceList : List (M e s a)
              -> M e s (List a)
  sequenceList [] = return []
  sequenceList (x :: xs) = return (!x :: !(sequenceList xs))

  public export
  sequenceVect : Vect n (M e s a)
              -> M e s (Vect n a)
  sequenceVect [] = return []
  sequenceVect (x :: xs) = return (!x :: !(sequenceVect xs))

  public export
  sequenceSnocList : SnocList (M e s a)
                  -> M e s (SnocList a)
  sequenceSnocList [<] = return [<]
  sequenceSnocList (xs :< x) = return (!(sequenceSnocList xs) :< !x)

  public export
  sequenceList1 : List1 (M e s a)
               -> M e s (List1 a)
  sequenceList1 (x ::: []) = return (singleton !x)
  sequenceList1 (x ::: y :: zs) = return (!x `cons` !(sequenceList1 (y ::: zs)))

  public export
  sequenceProduct : (M e s a, M e s b)
                 -> M e s (a, b)
  sequenceProduct (f, g) = return (!f, !g)

  public export
  sequenceEither : Either (M e s a) (M e s b)
                -> M e s (Either a b)
  sequenceEither (Left f)  = return (Left !f)
  sequenceEither (Right g) = return (Right !g)

  ||| Run a computation for each element of the list and join the results.
  public export
  forList : List a -> (a -> M e s b) -> M e s (List b)
  forList xs f = sequenceList (map f xs)

  ||| Run a computation for each element of the pair and join the results.
  public export
  forProduct : (a, b)
            -> (a -> M e s a')
            -> (b -> M e s b')
            -> M e s (a', b')
  forProduct p f g = sequenceProduct (bimap f g p)

  public export
  traverseProduct : (a -> M e s a')
                 -> (b -> M e s b')
                 -> (a, b)
                 -> M e s (a', b')
  traverseProduct f g p = forProduct p f g

  public export
  forCatMaybes : List a
              -> (a -> M e s (Maybe b))
              -> M e s (List b)
  forCatMaybes list f =
    mapResult catMaybes (forList list f)

  ||| Run a computation for each element of the List1 and join the results.
  public export
  forList1 : List1 a -> (a -> M e s b) -> M e s (List1 b)
  forList1 xs f = sequenceList1 (map f xs)

  ||| Run a computation for each element of the SnocList and join the results.
  public export
  forSnocList : SnocList a -> (a -> M e s b) -> M e s (SnocList b)
  forSnocList xs f = sequenceSnocList (map f xs)

  public export
  traverseSnocList : (a -> M e s b)
                  -> SnocList a
                  -> M e s (SnocList b)
  traverseSnocList f xs = forSnocList xs f

  public export
  traverseList : (a -> M e s b)
              -> List a
              -> M e s (List b)
  traverseList f xs = forList xs f

  public export
  traverseList1 : (a -> M e s b)
               -> List1 a
               -> M e s (List1 b)
  traverseList1 f xs = forList1 xs f

  public export
  traverseList_ : (a -> M e s ())
               -> List a
               -> M e s ()
  traverseList_ f xs = discard $ traverseList f xs

  public export
  traverseList1_ : (a -> M e s ())
                -> List1 a
                -> M e s ()
  traverseList1_ f xs = discard $ traverseList1 f xs

  ||| Run a computation for each element of the Vect and join the results.
  public export
  forVect : Vect n a -> (a -> M e s b) -> M e s (Vect n b)
  forVect xs f = sequenceVect (map f xs)

  ||| Run a computation for each element of the Maybe and join the results.
  public export
  forMaybe : Maybe a -> (a -> M e s b) -> M e s (Maybe b)
  forMaybe mb f = sequenceMaybe (map f mb)

  public export
  traverseMaybe : (a -> M e s b)
               -> Maybe a
               -> M e s (Maybe b)
  traverseMaybe f m = forMaybe m f

  public export
  forList_ : List a -> (a -> M e s b) -> M e s ()
  forList_ xs f = discard $ forList xs f

  public export
  forSnocList_ : SnocList a -> (a -> M e s b) -> M e s ()
  forSnocList_ xs f = discard $ forSnocList xs f

  public export
  forVect_ : Vect n a -> (a -> M e s b) -> M e s ()
  forVect_ xs f = discard $ forVect xs f

  public export
  filterMaybeListM : List a -> (a -> M e s (Maybe b)) -> M e s (List b)
  filterMaybeListM [] f = return []
  filterMaybeListM (x :: xs) f = M.do
    rest <- filterMaybeListM xs f
    r <- f x
    case r of
      Nothing => return rest
      Just x' => return (x' :: rest)

  ||| Never fails.
  public export
  try : M e s a -> M e s (Either e a)
  try m = \(ch, s) => Prelude.do
    case !(m (ch, s)) of
      (ch, Left x) => pure (ch, Right (s, Left x))
      (ch, Right (s, x)) => pure (ch, Right (s, Right x))

  ||| Either one must work. Tries the left one first.
  public export
  one : M e s a -> M e s b -> M e s (Either a b)
  one f g = M.do
   case !(try f) of
     Right x => return (Left x)
     Left _ => g <&> Right

  ||| Both must work. Tries the left one first.
  public export
  both : M e s a -> M e s b -> M e s (a, b)
  both f g = (f <&> (,)) <*> g

  ||| First working alternative.
  public export
  (<|>) : M e s a -> M e s a -> M e s a
  (f <|> g) = one f g <&> fromEither

  public export
  allList : List (M e s Bool) -> M e s Bool
  allList [] = return True
  allList (x :: xs) = M.do
    x <- x
    case x of
      False => return False
      True => allList xs

  ||| Lazy logical disjunction.
  public export
  or : M e s Bool -> M e s Bool -> M e s Bool
  or a b = M.do
    case !a of
      True => return True
      False => b

  infixr 8 `and`

  infixr 7 `or`

  ||| Lazy logical conjunction.
  public export
  and : M e s Bool -> M e s Bool -> M e s Bool
  and a b = M.do
    case !a of
      True => b
      False => return False

  public export
  io : IO a -> M e s a
  io cmd (ch, s) = Prelude.do
    r <- cmd
    pure (ch, Right (s, r))

  public export
  data OutputMode = STDOUT | FILE String

  ||| Eagerly prints something out (using IO) on the given channel.
  public export
  print_ : Channel -> OutputMode -> String -> M e s ()
  print_ ch mode str = M.do
    when !(isListening ch) $ M.do
      case mode of
        STDOUT => io $ putStrLn str
        FILE file => discard $ io $ appendFile {io = IO} file str

  public export
  timestamp : M e s (Clock Process)
  timestamp = io $ clockTime Process

  public export
  gcTimestamp : FromString e => M e s (Clock GCCPU)
  gcTimestamp = M.do
    Just x <- io $ clockTime GCCPU
      | _ => throw ("GC CPU-time not supported")
    return x

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
  clock : FromString e => String -> M e s a -> M e s a
  clock msg m = M.do
    t0 <- timestamp
    t0' <- gcTimestamp
    r <- m
    t1 <- timestamp
    t1' <- gcTimestamp
    let dif = timeDifference t1 t0
    let dif' = timeDifference t1' t0'
    print_ Timing STDOUT "\{msg} took overall-time: \{formatted dif}; gc time: \{formatted dif'}"
    return r

  ||| Clocks the given computation when the condition is true, prints out (eagerly) the time it took to run the computation.
  public export
  clockWhen : FromString e => Bool -> String -> M e s a -> M e s a
  clockWhen False msg m = m
  clockWhen True msg m = clock msg m

  public export
  clockThresholdD : FromString e => (a -> M e s String) -> Integer -> M e s a -> M e s a
  clockThresholdD msg threshold m = M.do
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
    when (workloadTime > threshold && toNano dif' > 0) $ M.do
      msg <- msg r
      print_ Timing STDOUT "\{msg} took overall-time: \{formatted dif}; gc time: \{formatted dif'}" -- ; workload time: \{show workloadTime}ns"
    return r

  ||| Clocks the given computation, prints out (eagerly) the time it took to run the computation.
  public export
  clockThreshold : FromString e => String -> Integer -> M e s a -> M e s a
  clockThreshold msg threshold m = M.do
    clockThresholdD (\x => return msg) threshold m

  ||| Currently, write is just an alias to print_ on *Debug* channel.
  ||| So all output of write is eagerly shown in console.
  public export
  write : String -> M e s ()
  write x = M.do
    print_ Debug STDOUT x

  ||| Computes the workload time (process time - GC time)
  public export
  time : FromString e => M e s a -> M e s (a, Clock Duration)
  time computation = M.do
   t0 <- timestamp
   t0' <- gcTimestamp
   x <- computation
   t1 <- timestamp
   t1' <- gcTimestamp
   let dif = timeDifference t1 t0
   let dif' = timeDifference t1' t0'
   let workloadTime = timeDifference dif dif'
   return (x, workloadTime)
