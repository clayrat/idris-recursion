module Augusteijn

import Data.CoList

import Iaia
import Iaia.Control
import Iaia.Native.Control

import Util

%default total

-- cata

data ListF : Type -> Type -> Type where
  NilF : ListF _ _
  Cons : a -> b -> ListF a b

Functor (ListF a) where
  map _ NilF       = NilF
  map f (Cons a b) = Cons a (f b)
  
Recursive (List a) (ListF a) where
  cata alg []        = alg NilF
  cata alg (x :: xs) = alg (Cons x (cata alg xs))

prodAlg : Algebra (ListF Integer) Integer
prodAlg NilF = 1
prodAlg (Cons a b) = a * b
  
prod : List Integer -> Integer
prod = cata prodAlg

rev : List a -> List a
rev = cata revAlg
  where
  revAlg NilF       = []
  revAlg (Cons x y) = y ++ [x]

-- ana  

Corecursive (List a) (ListF a) where
  ana coalg a = 
    case coalg a of 
      NilF => []
      Cons x l => x :: assert_total (ana coalg l)

Corecursive (CoList a) (ListF a) where
  ana coalg a = 
    case coalg a of 
      NilF => []
      Cons x l => x :: ana coalg l

countCoalg : Coalgebra (ListF Integer) Integer
countCoalg 0 = NilF
countCoalg n = Cons n (n-1)      

count : Integer -> List Integer
count = ana countCoalg

countC : Integer -> CoList Integer
countC = ana countCoalg

mutual 
  primCoalg : Coalgebra (ListF Integer) (List Integer)
  primCoalg [] = NilF
  primCoalg (x :: y) = Cons x (sieve (filter (notdiv x) y))

  sieve : List Integer -> List Integer
  sieve = ana primCoalg
    
primes : Integer -> List Integer
primes n = sieve [2..n]

mutual 
  primCoalgC : Coalgebra (ListF Integer) (CoList Integer)
  primCoalgC [] = NilF
  primCoalgC (x :: y) = Cons x (sieveC (filterCo (notdiv x) y))

  sieveC : CoList Integer -> CoList Integer
  sieveC = ana primCoalgC
    
primesC : CoList Integer
primesC = sieveC $ unfoldr (\n => Just (n, n+1)) 2

-- hylo 

factorial : Integer -> Integer
factorial = assert_total $ hylo prodAlg countCoalg

powah : Integer -> Integer -> Integer
powah x n = assert_total $ fst $ hylo prodFstAlg copiesCoalg (x,n)
  where 
  prodFstAlg : Algebra (ListF (Integer, Integer)) (Integer, Integer)
  prodFstAlg NilF = (1, 0)
  prodFstAlg (Cons (x,_) (y,_)) = (x * y, 0)

  copiesCoalg : Coalgebra (ListF (Integer, Integer)) (Integer, Integer)
  copiesCoalg (x, 0) = NilF
  copiesCoalg (x, n) = Cons (x, n) (x, n-1)
