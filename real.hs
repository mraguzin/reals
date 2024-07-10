{-# LANGUAGE TypeFamilies, FlexibleInstances, DataKinds, UndecidableInstances #-}
module ComputableReals where
import Data.Ratio


data Nat =
    Zero
  | Succ Nat
  deriving (Eq, Ord, Show)

one = Succ Zero

instance Num Nat where
    a + Zero = a
    a + (Succ b) = Succ (a + b)

    a - Zero = a
    a - (Succ b) = pred (a - b) -- modificirano oduzimanje

    a * Zero = Zero
    a * (Succ b) = a * b + a

    abs n = n

    signum Zero = Zero
    signum _    = one

    fromInteger n | n < 0  = undefined
                  | n == 0 = Zero
                  | n > 0  = Succ $ fromInteger (pred n)

    negate n = n

instance Enum Nat where
    toEnum 0 = Zero
    toEnum n | n < 0     = undefined
             | otherwise = Succ $ toEnum (pred n)

    fromEnum Zero     = 0
    fromEnum (Succ n) = succ $ fromEnum n

    succ n = Succ n

    pred Zero     = Zero
    pred (Succ n) = n

instance Integral Nat where
    toInteger Zero     = 0
    toInteger (Succ n) = succ $ toInteger n

    quotRem x Zero = (x, Zero)
    quotRem x y = sub x y Zero
     where sub x y c | y > x = (c, x)
                     | otherwise = sub (x - y) y (succ c)
    
    divMod = quotRem

instance Real Nat where
    toRational n = toRational $ fromEnum n

-- apsolutna razlika
absDiff :: Nat -> Nat -> Nat
absDiff x y = (x - y) + (y - x)

-- polimorfno potenciranje
pow :: Num a => a -> Nat -> a
pow _ 0        = 1
pow x (Succ n) = x * pow x n

-- sg potez
sgc :: Nat -> Nat
sgc n = 1 - signum n


data Fun1 a where
    Fun1 :: (Nat -> a) -> Fun1 a

data Fun2 a where
    Fun2 :: (Nat -> Nat -> a) -> Fun2 a

data Fun3 a where
    Fun3 :: (Nat -> Nat -> Nat -> a) -> Fun3 a

-- ograničena podrška za vektorske funkcije
-- kodomena može biti N^k; mi idemo do k=2
type Fun12 a = Fun1 (a,a)
type Fun22 a = Fun2 (a,a)

-- primjer proširenja operacija na vektore (nije dio IA)
instance Num a => Num (a,a) where
    (x,y) + (x',y') = (x+x', y+y')
    (x,y) - (x',y') = (x-x', y-y')
    (x,y) * (x',y') = (x*x', y*y')
    abs (x,y) = (abs x, abs y)
    signum (x,y) = (signum x, signum y)
    negate (x,y) = (negate x, negate y)
    fromInteger i = undefined

instance Fractional a => Fractional (a,a) where
    fromRational x = undefined
    recip (x,y) = (recip x, recip y)

-- data Fun k where
--     Fun :: f -> NFun k

class RingFun2 a where -- ovakvih klasa treba biti onoliko koliko
                       --i mjesnosti k (k > 1) za funkcije
    minFun2  :: (Nat -> Nat) -> Fun2 a -> Nat -> a
    maxFun2  :: (Nat -> Nat) -> Fun2 a -> Nat -> a
    sumFun2  :: (Nat -> Nat) -> (Nat -> Nat) -> Fun2 a -> Nat -> a
    prodFun2 :: (Nat -> Nat) -> (Nat -> Nat) -> Fun2 a -> Nat -> a

class RingFun3 a where
    minFun3  :: (Nat -> Nat -> Nat) -> Fun3 a -> Nat -> Nat -> a
    maxFun3  :: (Nat -> Nat -> Nat) -> Fun3 a -> Nat -> Nat -> a
    sumFun3  :: (Nat -> Nat -> Nat) -> (Nat -> Nat -> Nat) -> Fun3 a -> Nat -> Nat -> a
    prodFun3 :: (Nat -> Nat -> Nat) -> (Nat -> Nat -> Nat) -> Fun3 a -> Nat -> Nat -> a

instance Num a => Num (Fun1 a) where
    (Fun1 f) + (Fun1 g) = Fun1 (\x -> f x + g x)
    (Fun1 f) - (Fun1 g) = Fun1 (\x -> f x - g x)
    (Fun1 f) * (Fun1 g) = Fun1 (\x -> f x * g x)
    abs (Fun1 f) = Fun1 (\x -> abs $ f x)
    signum (Fun1 f) = Fun1 (\x -> signum $ f x)
    negate (Fun1 f) = Fun1 (\x -> negate $ f x)
    fromInteger i = Fun1 (\_ -> fromInteger i)

instance Num a => Num (Fun2 a) where
    (Fun2 f) + (Fun2 g) = Fun2 (\x y -> f x y + g x y)
    (Fun2 f) - (Fun2 g) = Fun2 (\x y -> f x y - g x y)
    (Fun2 f) * (Fun2 g) = Fun2 (\x y -> f x y * g x y)
    abs (Fun2 f) = Fun2 (\x y -> abs $ f x y)
    signum (Fun2 f) = Fun2 (\x y -> signum $ f x y)
    negate (Fun2 f) = Fun2 (\x y -> negate $ f x y)
    fromInteger i = Fun2 (\_ _ -> fromInteger i)

instance Num a => Num (Fun3 a) where
    (Fun3 f) + (Fun3 g) = Fun3 (\x y z -> f x y z + g x y z)
    (Fun3 f) - (Fun3 g) = Fun3 (\x y z -> f x y z - g x y z)
    (Fun3 f) * (Fun3 g) = Fun3 (\x y z -> f x y z * g x y z)
    abs (Fun3 f) = Fun3 (\x y z -> abs $ f x y z)
    signum (Fun3 f) = Fun3 (\x y z -> signum $ f x y z)
    negate (Fun3 f) = Fun3 (\x y z -> negate $ f x y z)
    fromInteger i = Fun3 (\_ _ _ -> fromInteger i)

instance (Num a, Ord a) => RingFun2 a where
    minFun2 alfa (Fun2 f) x = minimum [f i x | i <- [0 .. alfa x]]
    maxFun2 alfa (Fun2 f) x = maximum [f i x | i <- [0 .. alfa x]]
    sumFun2 alfa beta (Fun2 f) x = sum [f i x | i <- [alfa x .. beta x]]
    prodFun2 alfa beta (Fun2 f) x = product [f i x | i <- [alfa x .. beta x]]

instance (Num a, Ord a) => RingFun3 a where
    minFun3 alfa (Fun3 f) x y = minimum [f i x y | i <- [0 .. alfa x y]]
    maxFun3 alfa (Fun3 f) x y = maximum [f i x y | i <- [0 .. alfa x y]]
    sumFun3 alfa beta (Fun3 f) x y = sum [f i x y | i <- [alfa x y .. beta x y]]
    prodFun3 alfa beta (Fun3 f) x y = product [f i x y | i <- [alfa x y .. beta x y]]

compose11 :: Fun1 a -> Fun1 Nat -> Fun1 a
compose11 (Fun1 f) (Fun1 g) = Fun1 (f . g)

compose12 :: Fun1 a -> Fun2 Nat -> Fun2 a
compose12 (Fun1 f) (Fun2 g) = Fun2 (\x y -> f $ g x y)

compose21 :: Fun2 a -> Fun12 Nat -> Fun1 a
compose21 (Fun2 f) (Fun1 g) = Fun1 (\x -> f (fst $ g x) (snd $ g x))

compose22 :: Fun2 a -> Fun22 Nat -> Fun2 a
compose22 (Fun2 f) (Fun2 g) = Fun2 (\x y -> f (fst $ g x y) (snd $ g x y))

apply1 :: Fun1 a -> Nat -> a
apply1 (Fun1 f) x = f x

apply2 :: Fun2 a -> Nat -> Nat -> a
apply2 (Fun2 f) x y = f x y

apply3 :: Fun3 a -> Nat -> Nat -> Nat -> a
apply3 (Fun3 f) x y z = f x y z

-- uzimamo da su funkcije oblika N^k -> Z implementirane koristeći Haskellov tip Integer
-- uzimamo da su funkcije oblika N^k -> Q implementirane koristeći Haskellov tip Rational
instance Fractional a => Fractional (Fun1 a) where
    recip (Fun1 f) = Fun1 (\x -> recip $ f x)
    fromRational x = Fun1 (\_ -> fromRational x)

instance Fractional a => Fractional (Fun2 a) where
    recip (Fun2 f) = Fun2 (\x y -> recip $ f x y)
    fromRational x = Fun2 (\_ _ -> fromRational x)

instance Fractional a => Fractional (Fun3 a) where
    recip (Fun3 f) = Fun3 (\x y z -> recip $ f x y z)
    fromRational x = Fun3 (\_ _ _ -> fromRational x)

-- realni brojevi
data CR where
    CR :: Fun1 Rational -> CR

approx :: CR -> Nat -> Rational
approx (CR f) k = apply1 f k

approxApply1 :: Fun1 CR -> Nat -> Nat -> Rational
approxApply1 (Fun1 f) x k = approx (f x) k

approxApply2 :: Fun2 CR -> Nat -> Nat -> Nat -> Rational
approxApply2 (Fun2 f) x y k = approx (f x y) k

approxApply3 :: Fun3 CR -> Nat -> Nat -> Nat -> Nat -> Rational
approxApply3 (Fun3 f) x y z k = approx (f x y z) k

instance Num CR where
    x + y = CR $ Fun1 (\k -> approx x (k+2) + approx y (k+2))
    (CR x) * (CR y) = CR (x * y)
    abs (CR x) = CR (abs x)
    signum (CR x) = undefined -- općenito nije izračunljivo (vidjeti IA)
    negate (CR x) = CR (negate x)
    fromInteger i = CR $ Fun1 (\_ -> toRational i)

instance Fractional CR where
    recip x = CR $ Fun1 (\k -> recip $ approx x (k+fi 0))
     where fi l | abs (approx x l) > toRational (3 % (pow 2 l)) = l
                | otherwise = fi (succ l)

    fromRational x = CR $ Fun1 (\_ -> x)

-- instance Num (Fun1 CR) where
--     (Fun1 f) + (Fun1 g) = Fun1 $ \x -> CR $ Fun1 (\k -> approx (f x) (succ (succ k)) + approx (g x) (succ (succ k)))
--     (Fun1 f) - (Fun1 g) = Fun1 $ \x -> CR $ Fun1 (\k -> approx (f x) (succ (succ k)) - approx (g x) (succ (succ k)))
--     (Fun1 f) * (Fun1 g) = Fun1 $ \x -> CR $ Fun1 (\k -> approx (f x) k * approx (g x) k)
--     abs (Fun1 f) = Fun1 $ \x -> CR $ Fun1 (\k -> abs (approx (f x) k))
--     signum _ = undefined
--     negate (Fun1 f) = Fun1 $ \x -> CR $ Fun1 (\k -> negate (approx (f x) k))
--     fromInteger i = Fun1 $ \_ -> CR $ Fun1 (\_ -> toRational i)

-- instance Num (Fun2 CR) where
--     (Fun2 f) + (Fun2 g) = Fun2 $ \x y -> CR $ Fun1 (\k -> approx (f x y) (succ (succ k)) + approx (g x y) (succ (succ k)))
--     (Fun2 f) - (Fun2 g) = Fun2 $ \x y -> CR $ Fun1 (\k -> approx (f x y) (succ (succ k)) - approx (g x y) (succ (succ k)))
--     (Fun2 f) * (Fun2 g) = Fun2 $ \x y -> CR $ Fun1 (\k -> approx (f x y) k * approx (g x y) k)
--     abs (Fun2 f) = Fun2 $ \x y -> CR $ Fun1 (\k -> abs (approx (f x y) k))
--     signum _ = undefined
--     negate (Fun2 f) = Fun2 $ \x y -> CR $ Fun1 (\k -> negate (approx (f x y) k))
--     fromInteger i = Fun2 $ \_ _ -> CR $ Fun1 (\_ -> toRational i)

-- instance Num (Fun3 CR) where
--     (Fun3 f) + (Fun3 g) = Fun3 $ \x y z -> CR $ Fun1 (\k -> approx (f x y z) (succ (succ k)) + approx (g x y z) (succ (succ k)))
--     (Fun3 f) - (Fun3 g) = Fun3 $ \x y z -> CR $ Fun1 (\k -> approx (f x y z) (succ (succ k)) - approx (g x y z) (succ (succ k)))
--     (Fun3 f) * (Fun3 g) = Fun3 $ \x y z -> CR $ Fun1 (\k -> approx (f x y z) k * approx (g x y z) k)
--     abs (Fun3 f) = Fun3 $ \x y z -> CR $ Fun1 (\k -> abs (approx (f x y z) k))
--     signum _ = undefined
--     negate (Fun3 f) = Fun3 $ \x y z -> CR $ Fun1 (\k -> negate (approx (f x y z) k))
--     fromInteger i = Fun3 $ \_ _ _ -> CR $ Fun1 (\_ -> toRational i)

instance RingFun2 CR where
    minFun2 alfa (Fun2 f) x = CR $ Fun1 (\k -> minimum [approx (f i x) k | i <- [0 .. alfa x]])
    maxFun2 alfa (Fun2 f) x = CR $ Fun1 (\k -> maximum [approx (f i x) k | i <- [0 .. alfa x]])
    sumFun2 alfa beta (Fun2 f) x = CR $ Fun1 (\k -> sum [approx (f i x) (k+beta x+1) | i <- [alfa x .. beta x]])
    prodFun2 alfa beta (Fun2 f) x = CR $ Fun1 (\k -> product [approx (f i x) k | i <- [alfa x .. beta x]])

instance RingFun3 CR where
    minFun3 alfa (Fun3 f) x y = CR $ Fun1 (\k -> minimum [approx (f i x y) k | i <- [0 .. alfa x y]])
    maxFun3 alfa (Fun3 f) x y = CR $ Fun1 (\k -> maximum [approx (f i x y) k | i <- [0 .. alfa x y]])
    sumFun3 alfa beta (Fun3 f) x y = CR $ Fun1 (\k -> sum [approx (f i x y) (k+beta x y+1) | i <- [alfa x y .. beta x y]])
    prodFun3 alfa beta (Fun3 f) x y = CR $ Fun1 (\k -> product [approx (f i x y) k | i <- [alfa x y .. beta x y]])

-- iščitavanje decimale *pozitivnog* realnog broja; PAZI: indekse decimala brojimo od 1, a ne od 0
decimalBase :: Nat -> CR -> Nat -> Nat
decimalBase b f n = mod (g (pow b n)) b
   where g :: Nat -> Nat
         g n = floor $ toRational n * abs (approx f (fi 0))
         fi k | u' (n * absnum (approx f k)) (absden (approx f k)) + toRational (sgc n) > toRational n * recip (toRational (pow 2 k)) = k
              | otherwise = fi (succ k)
         u' :: Nat -> Nat -> Rational
         u' x y = toRational $ min ((x % l y) - floor (x % l y) % 1) (floor (x % l y) % 1 + 1 - (x % l y))
         l :: Nat -> Nat
         l n = n + sgc n
         absnum :: Rational -> Nat
         absnum x = fromInteger $ abs (numerator x)
         absden :: Rational -> Nat
         absden x = fromInteger $ abs (denominator x)

decimal = decimalBase 10
binary = decimalBase 2

-- prikaz proizvoljno mnogo decimala pozitivnog realnog broja (uključujući i cjelobrojni dio)
showReal :: CR -> Nat -> String
showReal f n = show int ++ ('.' : decimals)
 where int = floor $ abs (approx f 1)
       decimals = [head $ show (decimal f i) | i <- [1 .. n]]


-- "promocije" funkcija N^k->N u N^k->Z
--                      N^k->Z u N^k->Q
--                      N^k->Q u N^k->R

fromNatural1 :: Fun1 Nat -> Fun1 Integer
fromNatural1 (Fun1 f) = Fun1 (\x -> toInteger $ f x)

fromNatural2 :: Fun2 Nat -> Fun2 Integer
fromNatural2 (Fun2 f) = Fun2 (\x y -> toInteger $ f x y)

fromNatural3 :: Fun3 Nat -> Fun3 Integer
fromNatural3 (Fun3 f) = Fun3 (\x y z -> toInteger $ f x y z)

fromIntegral1 :: Fun1 Integer -> Fun1 Rational
fromIntegral1 (Fun1 f) = Fun1 (\x -> toRational $ f x)

fromIntegral2 :: Fun2 Integer -> Fun2 Rational
fromIntegral2 (Fun2 f) = Fun2 (\x y -> toRational $ f x y)

fromIntegral3 :: Fun3 Integer -> Fun3 Rational
fromIntegral3 (Fun3 f) = Fun3 (\x y z -> toRational $ f x y z)

fromRational1 :: Fun1 Rational -> Fun1 CR
fromRational1 (Fun1 f) = Fun1 (\x -> CR $ Fun1 (\_ -> f x))

fromRational2 :: Fun2 Rational -> Fun2 CR
fromRational2 (Fun2 f) = Fun2 (\x y -> CR $ Fun1 (\_ -> f x y))

fromRational3 :: Fun3 Rational -> Fun3 CR
fromRational3 (Fun3 f) = Fun3 (\x y z -> CR $ Fun1 (\_ -> f x y z))


-- izračunljive funkcije sa R u R

-- data FunR where
--     FunR :: (CR -> CR) -> FunR

poly :: [CR] -> (CR -> CR)
poly [] = undefined
poly as = \x -> g x 0 as
 where g :: CR -> Nat -> [CR] -> CR
       g _ _ [] = 0
       g x i (a:as) = pow x i * a + g x (succ i) as

-- pomoćne funkcije za račun redova potencija
-- vidi Weihrauch, Computable Analysis Theorem 4.3.7
lim :: Fun1 CR -> (Nat -> Nat) -> CR
lim f e = CR $ Fun1 (\i -> approx (apply1 f (e (2+i))) (2+i))

slim :: Fun1 CR -> (Nat -> Nat) -> CR
slim xs e = lim (ss xs) e
 where ss :: Fun1 CR -> Fun1 CR
       ss f = Fun1 $ \i -> sum [apply1 f j | j <- [0 .. i]]

-- računanje reda potencija sa zadanim parametrima s, r:
-- |x| < s < r < R (R=radijus konvergencije)
-- vidi Theorem 4.3.11
series :: Fun1 CR -> Rational -> Rational -> Nat -> CR -> CR
series f r s m x = slim (g f x) (h' r s m)
 where g :: Fun1 CR -> CR -> Fun1 CR
       g a x' = Fun1 $ \i -> apply1 a i * pow x' i
       h :: Rational -> Rational -> Nat -> Nat -> Nat
       h r s m n = search 0
        where search k | toRational m * (pow (s / r) k) * (r / (r-s)) <= recip (toRational (pow 2 n)) = k
                       | otherwise = search (succ k)
       h' :: Rational -> Rational -> Nat -> (Nat -> Nat)
       h' r s m = \i -> h r s m i

-- implementacija svih elementarnih funkcija (Haskell generira preostale)
instance Floating CR where
    asin x = series (Fun1 coeff) 1 s 1 x
     where coeff :: Nat -> CR
           coeff n | odd n = fromRational $ toRational $ (oddp n) % ((evenp n) * n)
                   | otherwise = 0
           evenp n = product [2, 4 .. n]
           oddp  n = product [1, 3 .. n-1]
           s = approx x (z+1) + toRational (recip (pow 10 z))
           z = findz 1
           findz i | decimal x i < 9 = i
                   | otherwise = findz (succ i)

    pi = 6 * asin (fromRational (toRational (1 % 2)))

    acos x = pi / 2 - asin x

    atan x = series (Fun1 coeff) 1 s 1 x
     where coeff :: Nat -> CR
           coeff n | odd n = fromRational $ toRational (1 % n)
                   | otherwise = 0
           s = approx x (z+1) + toRational (recip (pow 10 z))
           z = findz 1
           findz i | decimal x i < 9 = i
                   | otherwise = findz (succ i)

    exp x = series (Fun1 coeff) (r (toRational (r k))) (s (toRational (r k))) (m k) x
     where coeff :: Nat -> CR
           coeff n = fromRational (toRational (1 % fact n))
           k = (floor (abs (approx x 1)) + 1) :: Nat
           r i = i + 1
           m i = pow (r i) (r i)
           s u = search 1
            where search i | (decimal x i) < 9 && apx < u = apx
                           | otherwise = search (succ i)
                   where apx = approx x (i+1) + toRational (recip (pow 10 i))

    sinh x = (exp x - exp (negate x)) / 2
    cosh x = (exp x + exp (negate x)) / 2
    
    log x = fromInteger (negate d) * log2 + log1 opt
     where log1 :: CR -> CR
           log1 x = series (Fun1 coeff) 1 s 1 (x-1)
             where coeff :: Nat -> CR
                   coeff n | n == 0 = 0
                           | otherwise = fromRational (toRational (pow (-1) (n+1) * (1 % n)))
                   s = approx x (z+1) + toRational (recip (pow 10 z))
                   z = findz 1
                   findz i | decimal x i < 9 = i
                           | otherwise = findz (succ i)
           pow' :: Nat -> Integer -> Rational
           pow' n x | x == 0 = 1 % 1
                    | x < 0  = recip (toRational x * pow' n (pred x))
                    | otherwise = toRational x * pow' n (pred x)
           (d, opt) = binsearch 0
           binsearch :: Integer -> (Integer, CR)
           binsearch i | (abs apx < (3 % 2)) && ((abs apx) > (1 % 2)) = (i, x * fromRational (pow' 2 i))
                       | abs apx < (1 % 2) = binsearch (succ i)
                       | otherwise = binsearch (pred i)
                        where apx = approx (x * fromRational (pow' 2 i)) (if i < 0 then 1 else fromInteger (i+1))
           log2 = log1 (fromRational $ 1+(1 % 3)) - log1 (fromRational $ 1-(1 % 3))


---------------------------------------- PRIMJERI ---------------------------------------

fact :: Nat -> Nat
fact Zero = one
fact (Succ n) = (fact n) * (Succ n)

fun' :: Nat -> Rational
fun' 0 = 0
fun' x = toRational x + 1 / toRational x

f = Fun1 fun'

p1 :: Fun2 Nat
p1 = Fun2 (\i _ -> i)

f' = sumFun2 (\_ -> 0) (\_ -> 5) p1

