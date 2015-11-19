{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import NumericPrelude

import Algebra.Additive
import Algebra.Algebraic
import Algebra.Field
import Algebra.Ring
import Algebra.Transcendental

import Control.Applicative
import Control.Comonad.Cofree

import Data.Foldable
import Data.Ratio
import Data.Traversable

--------------------------------------------------------------------------------
-- Part 1
--------------------------------------------------------------------------------

data Dual = Dual Double Double deriving (Ord, Eq)

instance Algebra.Additive.C Dual where
  zero                      = Dual 0 0
  (Dual f f') + (Dual g g') = Dual (f + g) (f' + g')
  (Dual f f') - (Dual g g') = Dual (f - g) (f' - g')
  negate (Dual f f')        = Dual (negate f) (negate f')

instance Algebra.Ring.C Dual where
  one                       = Dual 1 0
  (Dual f f') * (Dual g g') = Dual (f*g) (f'*g + g'*f)
  fromInteger n             = Dual (fromInteger n) 0
  (Dual f f') ^ n           = Dual (f^n) (fromInteger n*f^(n-1)*f')

instance Algebra.Field.C Dual where
  (Dual f f') / (Dual g g') = Dual (f/g) ((f'*g - g'*f)/g^2)
  recip (Dual f f')         = Dual (1/f) (f'/f^2)
  fromRational' x           = Dual (fromRational' x) zero
  (Dual f f') ^- n          = Dual (1/f^n) (negate one*fromInteger n*f^(n-1)*f')

instance Algebra.Algebraic.C Dual where
  sqrt (Dual f f')          = Dual (sqrt f) (f'*negate one/sqrt f)
  root n (Dual f f')        = Dual (root n f) (f*root (n-1) f'/fromInteger n)

instance Algebra.Transcendental.C Dual where
  pi                             = Dual pi zero
  exp (Dual f f')                = Dual (exp f) (f'*exp f)
  log (Dual f f')                = Dual (log f) (f'/f)
  logBase (Dual n _) (Dual f f') = Dual (logBase n f) (f'/(f*log n))
  (Dual f f') ** (Dual x _)      = Dual (f**x) (x*f**(x-1)*f')
  sin (Dual f f')                = Dual (sin f) (cos f*f')
  cos (Dual f f')                = Dual (cos f) (-1*sin f*f')
  tan (Dual f f')                = Dual (tan f) (1/(cos f)^2*f')
  asin (Dual f f')               = Dual (asin f) (f'/sqrt (1-f^2))
  atan (Dual f f')               = Dual (atan f) (f'/(1+f^2))
  acos (Dual f f')               = Dual (acos f) (-f'/sqrt (1-f^2))
  sinh (Dual f f')               = Dual (sinh f) (f'*cosh f)
  cosh (Dual f f')               = Dual (cosh f) (f'*sinh f)
  tanh (Dual f f')               = Dual (tanh f) (f'*cosh f)
  asinh (Dual f f')              = Dual (asinh f) (f'/sqrt (1+f^2))
  acosh (Dual f f')              = Dual (acosh f) (f'/(sqrt (1-f^2)*sqrt (1+f^2)))
  atanh (Dual f f')              = Dual (atanh f) (f'/(1-f^2))

diff' :: (Dual -> Dual) -> Double -> (Double, Double)
diff' f x = (y,d)
  where (Dual y d) = f (Dual x 1)

diff :: (Dual -> Dual) -> Double -> Double
diff f x = snd $ diff' f x

h :: Dual -> Dual
h x = 3 * x^4

lift r = Dual r 0

--------------------------------------------------------------------------------
-- Part 2
--------------------------------------------------------------------------------

data Tower a = a :> Tower a
             deriving (Functor, Foldable, Traversable)

instance Show a => Show (Tower a) where
  show (a :> _) = show a

tangents :: Tower a -> Tower a
tangents (_ :> as) = as

bundle :: a -> Tower a -> Tower a
bundle a as = a :> as

liftT :: a -> Tower a
liftT a = a :> liftT a

instance Algebra.Additive.C a => Algebra.Additive.C (Tower a) where
  zero = liftT zero
  x + y = add x y
    where add (a :> as) (b :> bs) = (a + b) :> add as bs
  x - y = sub x y
    where sub (a :> as) (b :> bs) = (a - b) :> sub as bs
  negate (a :> as) = negate a :> negate as

instance Algebra.Ring.C a => Algebra.Ring.C (Tower a) where
  one = bundle one zero
  fromInteger n = bundle (fromInteger n) zero
  p@(a :> a') * q@(b :> b') = (a*b) :> (p*b' + a'*q)
  p@(x :> x') ^ n | n < 0 = error "ACK"
                  | n == 0 = p
                  | otherwise = (x^n) :> (fromInteger n*p^(n-1)*x')

val :: Tower t -> t
val (a :> _) = a

df :: Tower a -> Tower a
df = tangents

dVar :: Algebra.Ring.C a => a -> Tower a
dVar x = bundle x (one :> zero)


dfs :: Algebra.Ring.C a => (Tower a -> Tower b) -> a -> [b]
dfs f = map val . iterate df . f . dVar

--------------------------------------------------------------------------------
-- Part 3
-- Attempt at simplified version of Edward Kmett's AD code.
--------------------------------------------------------------------------------

data Jet f a = a :- Jet f (f a)
             deriving Functor

bind :: (Traversable t, Algebra.Ring.C b)
        => (t (Tower b) -> c)
        -> t b
        -> t c
bind f as = snd $ mapAccumL outer (0 :: Int) as
  where outer i _ = (i+1, f . snd $ mapAccumL (inner i) 0 as)
        inner i j a = (j+1, if i == j then bundle a one else bundle a zero)

grad :: (Traversable f, Algebra.Ring.C a)
        => (f (Tower a) -> Tower b)
        -> f a
        -> f b
grad f = fmap val . bind (tangents . f)

jacobian :: (Functor f, Traversable t, Algebra.Ring.C b) => (t (Tower b) -> f (Tower b1)) -> t b -> t (f b1)
jacobian f = bind (fmap (val . tangents) . f)

hessian :: (Traversable f, Algebra.Ring.C b) => (f (Tower (Tower b)) -> Tower (Tower b1)) -> f b -> f (f b1)
hessian f = bind (fmap (val . tangents . tangents) . bind (val . tangents . f))

headJet :: Jet f a -> a
headJet (a :- _) = a

tailJet :: Jet f a -> Jet f (f a)
tailJet (_ :- as) = as

main :: IO ()
main = putStrLn "Hello, world!"

