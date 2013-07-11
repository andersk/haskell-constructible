{-# LANGUAGE
  DataKinds,
  DeriveDataTypeable,
  FlexibleInstances,
  GADTs,
  MultiParamTypeClasses,
  TemplateHaskell,
  TypeFamilies #-}

{- |
Module      :  Data.Real.Constructible
Description :  Constructible real numbers
Copyright   :  © Anders Kaseorg, 2013
License     :  BSD-style

Maintainer  :  Anders Kaseorg <andersk@mit.edu>
Stability   :  experimental
Portability :  Non-portable (GHC extensions)

The constructible reals, 'Construct', are the subset of the real
numbers that can be represented exactly using field operations
(addition, subtraction, multiplication, division) and positive square
roots.  They support exact computations, equality comparisons, and
ordering.

>>> [((1 + sqrt 5)/2)^n - ((1 - sqrt 5)/2)^n :: Construct | n <- [1..10]]
[sqrt 5,sqrt 5,2*sqrt 5,3*sqrt 5,5*sqrt 5,8*sqrt 5,13*sqrt 5,21*sqrt 5,34*sqrt 5,55*sqrt 5]

>>> let f (a, b, t, p) = ((a + b)/2, sqrt (a*b), t - p*((a - b)/2)^2, 2*p)
>>> let (a, b, t, p) = f . f . f . f $ (1, 1/sqrt 2, 1/4, 1 :: Construct)
>>> floor $ ((a + b)^2/(4*t))*10**40
31415926535897932384626433832795028841971

>>> let qf (p, q) = ((p + sqrt (p^2 - 4*q))/2, (p - sqrt (p^2 - 4*q))/2 :: Construct)
>>> let [(v, w), (x, _), (y, _), (z, _)] = map qf [(-1, -4), (v, -1), (w, -1), (x, y)]
>>> z/2
-1/16 + 1/16*sqrt 17 + 1/8*sqrt (17/2 - 1/2*sqrt 17) + 1/4*sqrt (17/4 + 3/4*sqrt 17 - (3/4 + 1/4*sqrt 17)*sqrt (17/2 - 1/2*sqrt 17))

Constructible complex numbers may be built from constructible reals
using 'Complex' from the complex-generic library.

>>> (z/2 :+ sqrt (1 - (z/2)^2))^17
1 :+ 0
-}

module Data.Real.Constructible (
  Construct,
  deconstruct,
  fromConstruct,
  ConstructException (..)) where

import Control.Applicative ((<$>), (<*>), (<|>), empty)
import Control.Exception (Exception, ArithException (..), throw)
import Data.Complex.Generic (Complex (..))
import Data.Complex.Generic.TH (deriveComplexF)
import Data.Ratio ((%), numerator, denominator)
import Data.Typeable (Typeable)
import Math.NumberTheory.Powers.Squares (exactSquareRoot)
import Numeric.Search.Integer (search)
import Text.Read (Lexeme (..), Read (..), lexP, parens, prec, readListPrecDefault, step)
import Text.Read.Lex (numberToInteger)

data FieldShape = QShape | SqrtShape !FieldShape deriving Show

data Field k where
  Q :: Field QShape
  Sqrt :: !(Field k) -> !(Elt k) -> Field (SqrtShape k)

instance Show (Field k) where
  showsPrec _ Q = showString "Q"
  showsPrec d (Sqrt k r) =
    showParen (d > 9) $ showsPrec 9 k . showString "[sqrt " . showsPrecK k 10 r . showString "]"

type family Elt (k :: FieldShape)
type instance Elt QShape = Rational
data SqrtElt k = SqrtZero | SqrtElt !(Elt k) !(Elt k)
type instance Elt (SqrtShape k) = SqrtElt k

sqrtElt :: Field k -> Elt k -> Elt k -> SqrtElt k
sqrtElt k a b | isZeroK k a && isZeroK k b = SqrtZero
              | otherwise = SqrtElt a b

sqrtLift :: Field k -> Elt k -> SqrtElt k
sqrtLift k a = sqrtElt k a (zeroK k)

addK :: Field k -> Elt k -> Elt k -> Elt k
addK Q a b = a + b
addK Sqrt{} SqrtZero a = a
addK Sqrt{} a SqrtZero = a
addK (Sqrt k _) (SqrtElt a b) (SqrtElt c d) = sqrtElt k (addK k a c) (addK k b d)

mulK :: Field k -> Elt k -> Elt k -> Elt k
mulK Q a b = a * b
mulK Sqrt{} SqrtZero _ = SqrtZero
mulK Sqrt{} _ SqrtZero = SqrtZero
mulK (Sqrt k r) (SqrtElt a b) (SqrtElt c d) =
  SqrtElt (addK k (mulK k a c) (mulK k r (mulK k b d))) (addK k (mulK k a d) (mulK k b c))

subK :: Field k -> Elt k -> Elt k -> Elt k
subK Q a b = a - b
subK k@Sqrt{} SqrtZero a = negateK k a
subK Sqrt{} a SqrtZero = a
subK (Sqrt k _) (SqrtElt a b) (SqrtElt c d) = sqrtElt k (subK k a c) (subK k b d)

negateK :: Field k -> Elt k -> Elt k
negateK Q a = negate a
negateK Sqrt{} SqrtZero = SqrtZero
negateK (Sqrt k _) (SqrtElt a b) = SqrtElt (negateK k a) (negateK k b)

absK :: Field k -> Elt k -> Elt k
absK Q a = abs a
absK k a = if sgnK k a == LT then negateK k a else a

signumK :: Field k -> Elt k -> Rational
signumK Q a = signum a
signumK k a = case sgnK k a of LT -> -1; EQ -> 0; GT -> 1

divK :: Field k -> Elt k -> Elt k -> Elt k
divK Q a b = a / b
divK k a b = mulK k a (recipK k b)

recipK :: Field k -> Elt k -> Elt k
recipK Q a = recip a
recipK Sqrt{} SqrtZero = throw DivideByZero
recipK (Sqrt k r) (SqrtElt a b) =
  let c = recipK k (subK k (mulK k a a) (mulK k r (mulK k b b)))
  in SqrtElt (mulK k a c) (mulK k (negateK k b) c)

eqK :: Field k -> Elt k -> Elt k -> Bool
eqK Q a b = a == b
eqK Sqrt{} SqrtZero SqrtZero = True
eqK (Sqrt k _) (SqrtElt a b) (SqrtElt c d) = eqK k a c && eqK k b d
eqK Sqrt{} SqrtZero SqrtElt{} = False
eqK Sqrt{} SqrtElt{} SqrtZero = False

isZeroK :: Field k -> Elt k -> Bool
isZeroK Q a = a == 0
isZeroK Sqrt{} SqrtZero = True
isZeroK Sqrt{} SqrtElt{} = False

compareK :: Field k -> Elt k -> Elt k -> Ordering
compareK Q a b = compare a b
compareK k a b = sgnK k (subK k a b)

sgnK :: Field k -> Elt k -> Ordering
sgnK Q a = compare a 0
sgnK Sqrt{} SqrtZero = EQ
sgnK (Sqrt k r) (SqrtElt a b) = case (sgnK k a, sgnK k b) of
  (o, EQ) -> o
  (EQ, o) -> o
  (GT, GT) -> GT
  (LT, LT) -> LT
  (GT, LT) -> sgnK k (subK k (mulK k a a) (mulK k r (mulK k b b)))
  (LT, GT) -> sgnK k (subK k (mulK k r (mulK k b b)) (mulK k a a))

zeroK :: Field k -> Elt k
zeroK Q = 0
zeroK Sqrt{} = SqrtZero

fromRationalK :: Field k -> Rational -> Elt k
fromRationalK Q a = a
fromRationalK (Sqrt k _) a = sqrtLift k (fromRationalK k a)

sqrtK :: Field k -> Elt k -> Maybe (Elt k)
sqrtK Q a = (%) <$> exactSquareRoot (numerator a) <*> exactSquareRoot (denominator a)
sqrtK Sqrt{} SqrtZero = return SqrtZero
sqrtK (Sqrt k r) (SqrtElt a b)
  | isZeroK k b = sqrtLift k <$> sqrtK k a <|> SqrtElt (zeroK k) <$> sqrtK k (divK k a r)
  | otherwise = do
    n <- sqrtK k $ subK k (mulK k a a) (mulK k r (mulK k b b))
    let half = fromRationalK k (1 % 2)
        p = mulK k half (addK k a n)
        q = mulK k half b
        y1 = do
          c <- sqrtK k p
          return (SqrtElt c (divK k q c))
        y2 = do
          d <- sqrtK k $ divK k p r
          return (SqrtElt (divK k q d) d)
    y1 <|> y2

negateS, sqrtS :: (Int -> ShowS) -> Int -> ShowS
(-!), (+!), (*!), (/!) :: (Int -> ShowS) -> (Int -> ShowS) -> Int -> ShowS
infixl 6 +!, -!
infixl 7 *!, /!
negateS s d = showParen (d > 6) $ showChar '-' . s 6
(+!) s1 s2 d = showParen (d > 6) $ s1 6 . showString " + " . s2 7
(-!) s1 s2 d = showParen (d > 6) $ s1 6 . showString " - " . s2 7
(*!) s1 s2 d = showParen (d > 7) $ s1 7 . showChar '*' . s2 8
(/!) s1 s2 d = showParen (d > 7) $ s1 7 . showChar '/' . s2 8
sqrtS s d = showParen (d > 9) $ showString "sqrt " . s 10

mulSqrtS :: Field k -> Elt k -> Elt k -> Int -> ShowS
mulSqrtS k b r
  | eqK k b (fromRationalK k 1) = sqrtS (flip (showsPrecK k) r)
  | otherwise = flip (showsPrecK k) b *! sqrtS (flip (showsPrecK k) r)

showsPrecK :: Field k -> Int -> Elt k -> ShowS
showsPrecK Q d x
  | q == 1 = showsPrec d p
  | p < 0 = negateS (flip showsPrec (-p) /! flip showsPrec q) d
  | otherwise = (flip showsPrec p /! flip showsPrec q) d
  where
    p = numerator x
    q = denominator x
showsPrecK Sqrt{} _ SqrtZero = showChar '0'
showsPrecK (Sqrt k r) d (SqrtElt a b) = case sgnK k b of
  EQ -> showsPrecK k d a
  GT | isZeroK k a -> mulSqrtS k b r d
     | otherwise -> (flip (showsPrecK k) a +! mulSqrtS k b r) d
  LT | isZeroK k a -> negateS (mulSqrtS k (negateK k b) r) d
     | otherwise -> (flip (showsPrecK k) a -! mulSqrtS k (negateK k b) r) d

fromRatioK :: Floating a => Field k -> Elt k -> Elt k -> a
fromRatioK Q = \a b -> fromRational (a/b)
fromRatioK (Sqrt k r) = er where
  e = fromRatioK k
  s = sqrt (e r (fromRationalK k 1))
  er SqrtZero _ = 0
  er _ SqrtZero = throw DivideByZero
  er (SqrtElt a0 b0) (SqrtElt a1 b1) = case (sgnK k a, sgnK k b) of
    (_, EQ) -> e a n1
    (EQ, _) -> e b n1*s
    (GT, GT) -> x1
    (LT, LT) -> x1
    (GT, LT) -> x2
    (LT, GT) -> x2
    where
      a = subK k (mulK k a0 a1) (mulK k r (mulK k b0 b1))
      b = subK k (mulK k b0 a1) (mulK k a0 b1)
      n0 = subK k (mulK k a0 a0) (mulK k r (mulK k b0 b0))
      n1 = subK k (mulK k a1 a1) (mulK k r (mulK k b1 b1))
      x1 = e a n1 + e b n1*s
      x2 = recip $ e a n0 - e b n0*s

fromConstructK :: Floating a => Field k -> Elt k -> a
fromConstructK k a = fromRatioK k a (fromRationalK k 1)

-- |The type of constructible real numbers.
data Construct where
  C :: !(Field k) -> !(Elt k) -> Construct

deconstructK :: Field k -> Elt k -> Either Rational (Construct, Construct, Construct)
deconstructK Q a = Left a
deconstructK Sqrt{} SqrtZero = Left 0
deconstructK (Sqrt k r) (SqrtElt a b)
  | isZeroK k b = deconstructK k a
  | otherwise = Right (C k a, C k b, C k r)

{- |
Deconstruct a constructible number as either a 'Rational', or a triple
@(a, b, r)@ of simpler constructible numbers representing @a + b*sqrt
r@ (with @b /= 0@ and @r > 0@).  Recursively calling 'deconstruct' on
all triples will yield a finite tree that terminates in 'Rational'
leaves.  Note that two constructible numbers that compare as equal may
deconstruct in different ways.
-}
deconstruct :: Construct -> Either Rational (Construct, Construct, Construct)
deconstruct (C k a) = deconstructK k a

data JoinK k1 k2 where
  JoinK :: !(Field k) -> (Elt k1 -> Elt k) -> (Elt k2 -> Elt k) -> JoinK k1 k2

joinK :: Field k1 -> Field k2 -> JoinK k1 k2
joinK Q k = JoinK k (fromRationalK k) id
joinK k Q = JoinK k id (fromRationalK k)
joinK k1 (Sqrt k2 r) = case joinK k1 k2 of
  JoinK k f1 f2 -> let r' = f2 r in case sqrtK k r' of
    Nothing ->
      let f2' SqrtZero = SqrtZero
          f2' (SqrtElt a b) = SqrtElt (f2 a) (f2 b)
      in JoinK (Sqrt k r') (sqrtLift k . f1) f2'
    Just s ->
      let f2' SqrtZero = zeroK k
          f2' (SqrtElt a b) = addK k (f2 a) (mulK k (f2 b) s)
      in JoinK k f1 f2'

instance Show Construct where
  showsPrec d (C k a) = showsPrecK k d a

instance Read Construct where
  readPrec =
    parens $
    pNum <|>
    prec 6 (pNegate <|> (step readPrec >>= pAddSub)) <|>
    prec 7 (step readPrec >>= pMulDiv) <|>
    prec 10 pSqrt
    where
      pNum = do {Number n <- lexP; maybe empty (return . fromInteger) (numberToInteger n)}
      pNegate = do {Symbol "-" <- lexP; a <- negate <$> step readPrec; return a <|> pAddSub a}
      pAddSub a = do {Symbol "+" <- lexP; b <- (a +) <$> step readPrec; return b <|> pAddSub b} <|>
                  do {Symbol "-" <- lexP; b <- (a -) <$> step readPrec; return b <|> pAddSub b}
      pMulDiv a = do {Symbol "*" <- lexP; b <- (a *) <$> step readPrec; return b <|> pMulDiv b} <|>
                  do {Symbol "/" <- lexP; b <- (a /) <$> step readPrec; return b <|> pMulDiv b}
      pSqrt = do {Ident "sqrt" <- lexP; a <- step readPrec; return (sqrt a)}
  readListPrec = readListPrecDefault

instance Eq Construct where
  C k1 a1 == C k2 a2 = case joinK k1 k2 of JoinK k f1 f2 -> eqK k (f1 a1) (f2 a2)

instance Ord Construct where
  compare (C k1 a1) (C k2 a2) = case joinK k1 k2 of JoinK k f1 f2 -> compareK k (f1 a1) (f2 a2)

instance Num Construct where
  C k1 a1 + C k2 a2 = case joinK k1 k2 of JoinK k f1 f2 -> C k (addK k (f1 a1) (f2 a2))
  C k1 a1 * C k2 a2 = case joinK k1 k2 of JoinK k f1 f2 -> C k (mulK k (f1 a1) (f2 a2))
  C k1 a1 - C k2 a2 = case joinK k1 k2 of JoinK k f1 f2 -> C k (subK k (f1 a1) (f2 a2))
  negate (C k x) = C k (negateK k x)
  abs (C k x) = C k (absK k x)
  signum (C k x) = C Q (signumK k x)
  fromInteger = C Q . fromInteger

instance Fractional Construct where
  C k1 a1 / C k2 a2 = case joinK k1 k2 of JoinK k f1 f2 -> C k (divK k (f1 a1) (f2 a2))
  recip (C k a) = C k (recipK k a)
  fromRational = C Q

-- |The type of exceptions thrown by impossible 'Construct' operations.
data ConstructException =
  -- |'toRational' was given an irrational constructible number.
  ConstructIrrational |
  -- |'sqrt' was given a negative constructible number.
  ConstructSqrtNegative |
  -- |'**' was given an exponent that is not a dyadic rational, or a transcendental function was called.
  Unconstructible String
  deriving (Eq, Ord, Typeable)

instance Show ConstructException where
  showsPrec _ ConstructIrrational = showString "cannot convert irrational Construct to rational"
  showsPrec _ ConstructSqrtNegative = showString "Construct sqrt: negative argument"
  showsPrec _ (Unconstructible s) = showString s . showString " is not constructible"

instance Exception ConstructException

{- |
This partial 'Floating' instance only supports 'sqrt' and '**' where
the exponent is a dyadic rational.  Passing a negative number to
'sqrt' will throw the 'ConstructSqrtNegative' exception.  All other
operations will throw the 'Unconstructible' exception.
-}
instance Floating Construct where
  sqrt (C k a)
    | sgnK k a == LT = throw ConstructSqrtNegative
    | otherwise = case sqrtK k a of
        Nothing -> C (Sqrt k a) (SqrtElt (zeroK k) (fromRationalK k 1))
        Just b -> C k b
  pi = throw (Unconstructible "pi")
  exp = throw (Unconstructible "exp")
  log = throw (Unconstructible "log")
  a ** b = go (numerator b') (denominator b') where
    b' = toRational b
    go p q = let (n, p') = divMod p q in
      (if n >= 0 then a^n else 1/a^(-n))*go' p' q
    go' 0 _ = 1
    go' p q = case divMod q 2 of
      (q', 0) -> sqrt (go p q')
      _ -> throw (Unconstructible "(** non-dyadic-rational)")
  logBase = throw (Unconstructible "logBase")
  sin = throw (Unconstructible "sin")
  tan = throw (Unconstructible "tan")
  cos = throw (Unconstructible "cos")
  asin = throw (Unconstructible "asin")
  atan = throw (Unconstructible "atan")
  acos = throw (Unconstructible "acos")
  sinh = throw (Unconstructible "sinh")
  tanh = throw (Unconstructible "tanh")
  cosh = throw (Unconstructible "cosh")
  asinh = throw (Unconstructible "asinh")
  atanh = throw (Unconstructible "atanh")
  acosh = throw (Unconstructible "acosh")

{- |
This 'Real' instance only supports 'toRational' on numbers that are in
fact rational.  'toRational' on an irrational number will throw the
'ConstructIrrational' exception.
-}
instance Real Construct where
  toRational = either id (\_ -> throw ConstructIrrational) . deconstruct

instance RealFrac Construct where
  properFraction (C Q x) = (m, C Q y) where (m, y) = properFraction x
  properFraction x = (fromInteger m, x - fromInteger m)
    where m = search ((> x) . fromInteger) - 1

instance Enum Construct where
  succ = (+ 1)
  pred = (subtract 1)
  toEnum = fromIntegral
  fromEnum = fromInteger . truncate
  enumFrom n = n `seq` (n : enumFrom (n + 1))
  enumFromThen n m = n `seq` m `seq` (n : enumFromThen m (m + m - n))
  enumFromTo n m = takeWhile (<= m) (enumFrom n)
  enumFromThenTo e1 e2 e3 = takeWhile predicate (enumFromThen e1 e2) where
    predicate | e2 >= e1 = (<= e3)
              | otherwise = (>= e3)

mk :: a -> a -> Complex a
mk = (:+)

toPair :: Complex a -> (a, a)
toPair (x :+ y) = (x, y)

deriveComplexF ''Complex ''Construct 'mk 'toPair

{- |
Evaluate a floating-point approximation for a constructible number.

To improve numerical stability, addition of numbers with different
signs is avoided using quadratic conjugation.

>>> fromConstruct $ sum (map sqrt [7, 14, 39, 70, 72, 76, 85]) - sum (map sqrt [13, 16, 46, 55, 67, 73, 79])
1.8837969820815017e-19
-}
fromConstruct :: Floating a => Construct -> a
fromConstruct (C k a) = fromConstructK k a
