module Text.Parser.Fork

import Data.Bool
import Data.List
import Data.Vect
import Data.Maybe
import Data.Nat
import public Data.List1

import public Control.Delayed
import public Text.Bounded

import public Text.Quantity
import public Text.Token

--------------------------------------------------------------------------------------
--------------- Fork of contrib/Text.Parser.Core & contrib/Text.Parser ---------------
--------------------------------------------------------------------------------------

||| Description of a language's grammar. The `tok` parameter is the type
||| of tokens, and the `consumes` flag is True if the language is guaranteed
||| to be non-empty - that is, successfully parsing the language is guaranteed
||| to consume some input.
export
data Grammar : (state : Type) -> (tok : Type) -> Type -> Type where
     Empty : (val : ty) -> Grammar state tok ty
     Terminal : String -> (tok -> Maybe a) -> Grammar state tok a
     NextIs : String -> (tok -> Bool) -> Grammar state tok tok
     EOF : Grammar state tok ()

     Fail : (location : Maybe Bounds) -> (fatal : Bool) -> String -> Grammar state tok ty
     Try : Grammar state tok ty -> Grammar state tok ty

     Commit : Grammar state tok ()
     MustWork : Grammar state tok a -> Grammar state tok a

     Bind : Grammar state tok a
         -> (a -> Grammar state tok b)
         -> Grammar state tok b
     Alt : Grammar state tok ty
        -> Lazy (Grammar state tok ty)
        -> Grammar state tok ty
     Bounds : Grammar state tok ty -> Grammar state tok (WithBounds ty)
     Position : Grammar state tok Bounds

     Set : state -> Grammar state tok ()
     Get : Grammar state tok state

||| Sequence two grammars. If either consumes some input, the sequence is
||| guaranteed to consume some input. If the first one consumes input, the
||| second is allowed to be recursive (because it means some input has been
||| consumed and therefore the input is smaller)
export %inline
(>>=) : Grammar state tok a
     -> (a -> Grammar state tok b)
     -> Grammar state tok b
(>>=) = Bind

||| Sequence two grammars. If either consumes some input, the sequence is
||| guaranteed to consume some input. If the first one consumes input, the
||| second is allowed to be recursive (because it means some input has been
||| consumed and therefore the input is smaller)
public export %inline %tcinline
(>>) : Grammar state tok ()
    -> Lazy (Grammar state tok a)
    -> Grammar state tok a
(>>) p q = Bind p (const q)

||| Sequence two grammars. If either consumes some input, the sequence is
||| guaranteed to consume input. This is an explicitly non-infinite version
||| of `>>=`.
export %inline
seq : Grammar state tok a
   -> (a -> Grammar state tok b)
   -> Grammar state tok b
seq = Bind

||| Sequence a grammar followed by the grammar it returns.
export %inline
join : Grammar state tok (Grammar state tok a)
    -> Grammar state tok a
join p = Bind p id

||| Allows the result of a grammar to be mapped to a different value.
export
Functor (Grammar state tok) where
  map f (Empty val)  = Empty (f val)
  map f (Fail bd fatal msg) = Fail bd fatal msg
  map f (Try g) = Try (map f g)
  map f (MustWork g) = MustWork (map f g)
  map f (Terminal msg g) = Terminal msg (map f . g)
  map f (Alt x y) = Alt (map f x) (map f y)
  map f (Bind act next)
      = Bind act (\val => map f (next val))
  map f (Bounds act) = Bind (Bounds act) (Empty . f)
  -- The remaining constructors (NextIs, EOF, Commit) have a fixed type,
  -- so a sequence must be used.
  map f p = Bind p (Empty . f)

||| Give two alternative grammars. If both consume, the combination is
||| guaranteed to consume.
export %inline
(<|>) : Grammar state tok ty
     -> Lazy (Grammar state tok ty)
     -> Grammar state tok ty
(<|>) = Alt

infixr 2 <||>
||| Take the tagged disjunction of two grammars. If both consume, the
||| combination is guaranteed to consume.
export
(<||>) : Grammar state tok a
      -> Lazy (Grammar state tok b)
      -> Grammar state tok (Either a b)
(<||>) p q = (Left <$> p) <|> (Right <$> q)

||| Sequence a grammar with value type `a -> b` and a grammar
||| with value type `a`. If both succeed, apply the function
||| from the first grammar to the value from the second grammar.
||| Guaranteed to consume if either grammar consumes.
export %inline
(<*>) : Grammar state tok (a -> b)
     -> Grammar state tok a
     -> Grammar state tok b
(<*>) x y = Bind x (\f => map f y)

||| Sequence two grammars. If both succeed, use the value of the first one.
||| Guaranteed to consume if either grammar consumes.
export %inline
(<*) : Grammar state tok a
    -> Grammar state tok b
    -> Grammar state tok a
(<*) x y = map const x <*> y

||| Sequence two grammars. If both succeed, use the value of the second one.
||| Guaranteed to consume if either grammar consumes.
export %inline
(*>) : Grammar state tok a
    -> Grammar state tok b
    -> Grammar state tok b
(*>) x y = map (const id) x <*> y

export %inline
get : Grammar state tok state
get = Get

export %inline
set : state -> Grammar state tok ()
set = Set

export %inline
update : (state -> state) -> Grammar state tok ()
update f = do
  st <- get
  set (f st)

export %inline
act : Semigroup state => state -> Grammar state tok ()
act x = do
  st <- get
  set (st <+> x)

||| Produce a grammar that can parse a different type of token by providing a
||| function converting the new token type into the original one.
export
mapToken : (a -> b) -> Grammar state b ty -> Grammar state a ty
mapToken f (Empty val) = Empty val
mapToken f (Terminal msg g) = Terminal msg (g . f)
mapToken f (NextIs msg g) = Bind (NextIs msg (g . f)) (Empty . f)
mapToken f EOF = EOF
mapToken f (Fail bd fatal msg) = Fail bd fatal msg
mapToken f (Try g) = Try (mapToken f g)
mapToken f (MustWork g) = MustWork (mapToken f g)
mapToken f Commit = Commit
mapToken f (Bind act next)
  = Bind (mapToken f act) (\x => mapToken f (next x))
mapToken f (Alt x y) = Alt (mapToken f x) (mapToken f y)
mapToken f (Bounds act) = Bounds (mapToken f act)
mapToken f Position = Position
mapToken f (Set action) = Set action
mapToken f Get = Get

||| Always succeed with the given value.
export %inline
pure : (val : ty) -> Grammar state tok ty
pure = Empty

||| Check whether the next token satisfies a predicate
export %inline
nextIs : String -> (tok -> Bool) -> Grammar state tok tok
nextIs = NextIs

||| Look at the next token in the input
export %inline
peek : Grammar state tok tok
peek = nextIs "Unrecognised token" (const True)

||| Succeeds if running the predicate on the next token returns Just x,
||| returning x. Otherwise fails.
export %inline
terminal : String -> (tok -> Maybe a) -> Grammar state tok a
terminal = Terminal

||| Always fail with a message
export %inline
fail : String -> Grammar state tok ty
fail = Fail Nothing False

||| Always fail with a message and a location
export %inline
failLoc : Bounds -> String -> Grammar state tok ty
failLoc b = Fail (Just b) False

||| Fail with no possibility for recovery (i.e.
||| no alternative parsing can succeed).
export %inline
fatalError : String -> Grammar state tok ty
fatalError = Fail Nothing True

||| Fail with no possibility for recovery (i.e.
||| no alternative parsing can succeed).
export %inline
fatalLoc : Bounds -> String -> Grammar state tok ty
fatalLoc b = Fail (Just b) True

||| Catch a fatal error
export %inline
try : Grammar state tok ty -> Grammar state tok ty
try = Try

||| Succeed if the input is empty
export %inline
eof : Grammar state tok ()
eof = EOF

||| Commit to an alternative; if the current branch of an alternative
||| fails to parse, no more branches will be tried
export %inline
commit : Grammar state tok ()
commit = Commit

||| If the parser fails, treat it as a fatal error
export %inline
mustWork : Grammar state tok ty -> Grammar state tok ty
mustWork = MustWork

export %inline
bounds : Grammar state tok ty -> Grammar state tok (WithBounds ty)
bounds = Bounds

export %inline
position : Grammar state tok Bounds
position = Position

public export
data ParsingError tok st = Error String st (Maybe Bounds)

export
Show tok => Show (ParsingError tok st) where
  show (Error s st Nothing) = "PARSING ERROR: " ++ s
  show (Error s st (Just (MkBounds startLine startCol endLine endCol))) =
    "PARSING ERROR: "
    ++ s
    ++ " @ L\{show startLine}:\{show startCol}-L\{show endLine}:\{show endCol}"

data ParseResult : Type -> Type -> Type -> Type where
     Failure : (committed : Bool)
            -> (fatal : Bool)
            -> List1 (ParsingError tok state)
            -> ParseResult state tok ty
     Res : state -> (committed : Bool) ->
           (val : WithBounds ty) -> (more : List (WithBounds tok)) -> ParseResult state tok ty

mergeWith : WithBounds ty -> ParseResult state tok sy -> ParseResult state tok sy
mergeWith x (Res s committed val more) = Res s committed (mergeBounds x val) more
mergeWith x v = v

doParse : state
       -> (commit : Bool)
       -> (act : Grammar state tok ty)
       -> (xs : List (WithBounds tok))
       -> ParseResult state tok ty
doParse s com (Empty val) xs = Res s com (irrelevantBounds val) xs
doParse s com (Fail location fatal str) xs
    = Failure com fatal (Error str s (location <|> (bounds <$> head' xs)) ::: Nil)
doParse s com (Try g) xs = case doParse s com g xs of
  -- recover from fatal match but still propagate the 'commit'
  Failure com _ errs => Failure com False errs
  res => res
doParse s com Commit xs = Res s True (irrelevantBounds ()) xs
doParse s com (MustWork g) xs =
  case assert_total (doParse s com g xs) of
       Failure com' _ errs => Failure com' True errs
       res => res
doParse s com (Terminal err f) [] = Failure com False (Error "End of input" s Nothing ::: Nil)
doParse s com (Terminal err f) (x :: xs) =
  case f x.val of
       Nothing => Failure com False (Error err s (Just x.bounds) ::: Nil)
       Just a => Res s com (const a <$> x) xs
doParse s com EOF [] = Res s com (irrelevantBounds ()) []
doParse s com EOF (x :: xs) = Failure com False (Error "Expected end of input" s (Just x.bounds) ::: Nil)
doParse s com (NextIs err f) [] = Failure com False (Error "End of input" s Nothing ::: Nil)
doParse s com (NextIs err f) (x :: xs)
      = if f x.val
           then Res s com (removeIrrelevance x) (x :: xs)
           else Failure com False (Error err s (Just x.bounds) ::: Nil)
doParse s com (Alt x y) xs
    = case doParse s False x xs of
           Failure com' fatal errs
              => if com' || fatal
                        -- If the alternative had committed, don't try the
                        -- other branch (and reset commit flag)
                   then Failure com fatal errs
                   else case (assert_total doParse s False y xs) of
                             (Failure com'' fatal' errs') =>
                               if com'' || fatal'
                                  -- Only add the errors together if the second branch
                                  -- is also non-committed and non-fatal.
                                  then Failure com'' fatal' errs'
                                  else Failure False False (errs ++ errs')
                             (Res s _ val xs) => Res s com val xs
           -- Successfully parsed the first option, so use the outer commit flag
           Res s _ val xs => Res s com val xs
doParse s com (Bind act next) xs
    = case assert_total (doParse s com act xs) of
           Failure com fatal errs => Failure com fatal errs
           Res s com v xs =>
             mergeWith v (assert_total $ doParse s com (next v.val) xs)
doParse s com (Bounds act) xs
    = case assert_total (doParse s com act xs) of
           Failure com fatal errs => Failure com fatal errs
           Res s com v xs => Res s com (const v <$> v) xs
doParse s com Position [] = Failure com False (Error "End of input" s Nothing ::: Nil)
doParse s com Position (x :: xs)
    = Res s com (irrelevantBounds x.bounds) (x :: xs)
doParse s com (Set action) xs = Res action com (irrelevantBounds ()) xs
doParse s com Get xs = Res s com (irrelevantBounds s) xs

||| Parse a list of tokens according to the given grammar. If successful,
||| returns a pair of the parse result and the unparsed tokens (the remaining
||| input).
export
parse : (act : Grammar () tok ty) -> (xs : List (WithBounds tok)) ->
        Either (List1 (ParsingError tok ())) (ty, List (WithBounds tok))
parse act xs
    = case doParse neutral False act xs of
           Failure _ _ errs => Left errs
           Res _ _ v rest => Right (v.val, rest)

export
parseWith : state
         -> (act : Grammar state tok ty)
         -> (xs : List (WithBounds tok))
         -> Either (List1 (ParsingError tok state)) (state, ty, List (WithBounds tok))
parseWith st act xs
    = case doParse st False act xs of
           Failure _ _ errs => Left errs
           Res s _ v rest => Right (s, v.val, rest)

-----------------------------------------
----------- Library code ----------------
-----------------------------------------

||| Parse a terminal based on a kind of token.
export
match : (Eq k, TokenKind k) =>
        (kind : k) ->
        Grammar state (Token k) (TokType kind)
match k = terminal "Unrecognised input" $
    \t => if t.kind == k
             then Just $ tokValue k t.text
             else Nothing

||| Optionally parse a thing, with a default value if the grammar doesn't
||| match. May match the empty input.
export
option : (def : a)
      -> (p : Grammar state tok a)
      -> Grammar state tok a
option def p = p <|> pure def

||| Optionally parse a thing.
||| To provide a default value, use `option` instead.
export
optional : (p : Grammar state tok a)
         -> Grammar state tok (Maybe a)
optional p = option Nothing (map Just p)

||| Try to parse one thing or the other, producing a value that indicates
||| which option succeeded. If both would succeed, the left option
||| takes priority.
export
choose : (l : Grammar state tok a)
      -> (r : Grammar state tok b)
      -> Grammar state tok (Either a b)
choose l r = map Left l <|> map Right r

||| Produce a grammar by applying a function to each element of a container,
||| then try each resulting grammar until the first one succeeds. Fails if the
||| container is empty.
export
choiceMap : (a -> Grammar state tok b)
          -> Foldable t
          => t a
          -> Grammar state tok b
choiceMap f xs = foldr (\x, acc => f x <|> acc)
                           (fail "No more options") xs

%hide Prelude.(>>=)

||| Try each grammar in a container until the first one succeeds.
||| Fails if the container is empty.
export
choice : Foldable t
      => t (Grammar state tok a)
      -> Grammar state tok a
choice = choiceMap id

mutual
  ||| Parse one or more things
  export
  some : Grammar state tok a
      -> Grammar state tok (List1 a)
  some p = pure (!p ::: !(many p))

  ||| Parse zero or more things (may match the empty input)
  export
  many : Grammar state tok a
      -> Grammar state tok (List a)
  many p = option [] (forget <$> some p)

mutual
  private
  count1 : (q : Quantity)
        -> (p : Grammar state tok a)
        -> Grammar state tok (List a)
  count1 q p = do x <- p
                  seq (count q p)
                      (\xs => pure (x :: xs))

  ||| Parse `p`, repeated as specified by `q`, returning the list of values.
  export
  count : (q : Quantity) ->
          (p : Grammar state tok a) ->
          Grammar state tok (List a)
  count (Qty Z Nothing) p = many p
  count (Qty Z (Just Z)) _ = pure []
  count (Qty Z (Just (S max))) p = option [] $ count1 (atMost max) p
  count (Qty (S min) Nothing) p = count1 (atLeast min) p
  count (Qty (S min) (Just Z)) _ = fail "Quantity out of order"
  count (Qty (S min) (Just (S max))) p = count1 (between (S min) max) p

mutual
  ||| Parse one or more instances of `p` until `end` succeeds, returning the
  ||| list of values from `p`. Guaranteed to consume input.
  export
  someTill : (end : Grammar state tok e) ->
             (p : Grammar state tok a) ->
             Grammar state tok (List1 a)
  someTill end p = do x <- p
                      seq (manyTill end p)
                          (\xs => pure (x ::: xs))

  ||| Parse zero or more instances of `p` until `end` succeeds, returning the
  ||| list of values from `p`. Guaranteed to consume input if `end` consumes.
  export
  manyTill : (end : Grammar state tok e) ->
             (p : Grammar state tok a) ->
             Grammar state tok (List a)
  manyTill end p = map (const []) end <|> (forget <$> someTill end p)

mutual
  ||| Parse one or more instance of `skip` until `p` is encountered,
  ||| returning its value.
  export
  afterSome : (skip : Grammar state tok s) ->
              (p : Grammar state tok a) ->
              Grammar state tok a
  afterSome skip p = do ignore $ skip
                        afterMany skip p

  ||| Parse zero or more instance of `skip` until `p` is encountered,
  ||| returning its value.
  export
  afterMany : (skip : Grammar state tok s) ->
              (p : Grammar state tok a) ->
              Grammar state tok a
  afterMany skip p = p <|> afterSome skip p

||| Parse one or more things, each separated by another thing.
export
sepBy1 : (sep : Grammar state tok s) ->
         (p : Grammar state tok a) ->
         Grammar state tok (List1 a)
sepBy1 sep p = [| p ::: many (sep *> p) |]

||| Parse zero or more things, each separated by another thing. May
||| match the empty input.
export
sepBy : (sep : Grammar state tok s) ->
        (p : Grammar state tok a) ->
        Grammar state tok (List a)
sepBy sep p = option [] $ forget <$> sepBy1 sep p

||| Parse one or more instances of `p` separated by and optionally terminated by
||| `sep`.
export
sepEndBy1 : (sep : Grammar state tok s)
         -> (p : Grammar state tok a)
         -> Grammar state tok (List1 a)
sepEndBy1 sep p = sepBy1 sep p <* optional sep

||| Parse zero or more instances of `p`, separated by and optionally terminated
||| by `sep`. Will not match a separator by itself.
export
sepEndBy : (sep : Grammar state tok s)
        -> (p : Grammar state tok a)
        -> Grammar state tok (List a)
sepEndBy sep p = option [] $ forget <$> sepEndBy1 sep p

||| Parse one or more instances of `p`, separated and terminated by `sep`.
export
endBy1 : (sep : Grammar state tok s)
      -> (p : Grammar state tok a)
      -> Grammar state tok (List1 a)
endBy1 sep p = some (p <* sep)

export
endBy : (sep : Grammar state tok s)
     -> (p : Grammar state tok a)
     -> Grammar state tok (List a)
endBy sep p = option [] $ forget <$> endBy1 sep p

||| Parse an instance of `p` that is between `left` and `right`.
export
between : (left : Grammar state tok l)
       -> (right : Grammar state tok r)
       -> (p : Grammar state tok a)
       -> Grammar state tok a
between left right contents = left *> contents <* right

export
location : Grammar state token (Int, Int)
location = startBounds <$> position

export
endLocation : Grammar state token (Int, Int)
endLocation = endBounds <$> position

export
column : Grammar state token Int
column = snd <$> location

public export
when : Bool -> Lazy (Grammar state token ()) -> Grammar state token ()
when True y = y
when False y = pure ()

public export
%inline
unless : Bool -> Lazy (Grammar state token ()) -> Grammar state token ()
unless = when . not

||| Read the token and succeed if it matches the predicate.
export
is : String -> (a -> Bool) -> Grammar s a a
is msg f = terminal msg (\x => toMaybe (f x) x)

||| Parse any token.
export
any : Grammar s tok tok
any = terminal "any token expected" (Just . id)

||| Parse any token, not defined by the given grammar.
export
not : Grammar s tok tok -> Grammar s tok tok
not g = do
  Nothing <- map Just g <|> pure Nothing
    | _ => fail "any token but"
  any

export
seqList : (gs : List (Grammar s tok a))
       -> Grammar s tok (List a)
seqList []        = [| [] |]
seqList (x :: xs) = [| x :: seqList xs |]

export
seqList1 : (gs : List1 (Grammar s tok a))
        -> Grammar s tok (List1 a)
seqList1 (x ::: xs) = [| x ::: seqList xs |]

export
seqVect : (gs : Vect n (Grammar s tok a))
       -> Grammar s tok (Vect n a)
seqVect []        = [| [] |]
seqVect (x :: xs) = [| x :: seqVect xs |]

public export
thatMany : (n : Nat) -> Grammar s tok a -> Grammar s tok (Vect n a)
thatMany n g = seqVect (replicate n g)

public export
guard : String -> Bool -> Grammar s tok ()
guard msg True = pure ()
guard msg False = fail msg
