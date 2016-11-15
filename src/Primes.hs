{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}

-- Stuff taken from the RSA module for now

module Primes where

import Data.Bits
import Data.Int
import Data.Word
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy as BS
import System.Random

os2ip :: ByteString -> Integer
os2ip x = BS.foldl (\ a b -> (256 * a) + (fromIntegral b)) 0 x

--instance Random Word8 where
--  randomR (a,b) g = let aI::Int = fromIntegral a 
--                        bI::Int = fromIntegral b
--                        (x, g') = randomR (aI, bI) g
--                    in (fromIntegral x, g')
--  random          = randomR (minBound, maxBound)

generate_pq :: RandomGen g => g -> Int64 -> (Integer, Integer, g)
generate_pq g len 
  | len < 2   = error "length to short for generate_pq"
  | p == q    = generate_pq g'' len
  | otherwise = (p, q, g'')
 where
  (baseP, g')  = large_random_prime g  (len `div` 2)
  (baseQ, g'') = large_random_prime g' (len - (len `div` 2))
  (p, q)       = if baseP < baseQ then (baseQ, baseP) else (baseP, baseQ)

large_random_prime :: RandomGen g => g -> Int64 -> (Integer, g)
large_random_prime g len = (prime, g''')
 where
  ([startH, startT], g') = random8s g 2
  (startMids, g'')       = random8s g' (len - 2)
  start_ls               = [startH .|. 0xc0] ++ startMids ++ [startT .|. 1]
  start                  = os2ip $ BS.pack start_ls
  (prime, g''')          = find_next_prime g'' start 
  
random8s :: RandomGen g => g -> Int64 -> ([Word8], g)
random8s g 0 = ([], g)
random8s g x = 
  let (rest, g') = random8s g (x - 1)
      (next8, g'') = random g'
  in (next8:rest, g'')

find_next_prime :: RandomGen g => g -> Integer -> (Integer, g)
find_next_prime g n
  | even n             = error "Even number sent to find_next_prime"
  | n `mod` 65537 == 1 = find_next_prime g (n + 2)
  | got_a_prime        = (n, g')
  | otherwise          = find_next_prime g' (n + 2)
 where
  (got_a_prime, g') = is_probably_prime g n

is_probably_prime :: RandomGen g => g -> Integer -> (Bool, g)
is_probably_prime !g !n 
  | any (\ x -> n `mod` x == 0) small_primes = (False, g)
  | otherwise                                = miller_rabin g n 20
 where
  small_primes = [   2,    3,    5,    7,   11,   13,   17,   19,   23,   29,
                    31,   37,   41,   43,   47,   53,   59,   61,   67,   71,
                    73,   79,   83,   89,   97,  101,  103,  107,  109,  113,
                   127,  131,  137,  139,  149,  151,  157,  163,  167,  173,
                   179,  181,  191,  193,  197,  199,  211,  223,  227,  229,
                   233,  239,  241,  251,  257,  263,  269,  271,  277,  281,
                   283,  293,  307,  311,  313,  317,  331,  337,  347,  349,
                   353,  359,  367,  373,  379,  383,  389,  397,  401,  409,
                   419,  421,  431,  433,  439,  443,  449,  457,  461,  463,
                   467,  479,  487,  491,  499,  503,  509,  521,  523,  541,
                   547,  557,  563,  569,  571,  577,  587,  593,  599,  601,
                   607,  613,  617,  619,  631,  641,  643,  647,  653,  659,
                   661,  673,  677,  683,  691,  701,  709,  719,  727,  733,
                   739,  743,  751,  757,  761,  769,  773,  787,  797,  809,
                   811,  821,  823,  827,  829,  839,  853,  857,  859,  863,
                   877,  881,  883,  887,  907,  911,  919,  929,  937,  941,
                   947,  953,  967,  971,  977,  983,  991,  997, 1009, 1013  ]

miller_rabin :: RandomGen g => g -> Integer -> Int -> (Bool, g)
miller_rabin g _ 0             = (True, g)
miller_rabin g n k | test a n  = (False, g')
                   | otherwise = miller_rabin g' n (k - 1)
 where
  (a, g') = randomR (2, n - 2) g
  base_b = tail $ reverse $ toBinary (n - 1) 
  -- 
  test a' n' = pow base_b a
   where
    pow   _  1 = False
    pow  []  _ = True 
    pow !xs !d = pow' xs d $ (d * d) `mod` n'
     where
      pow' _          !d1 !d2 | d2==1 && d1 /= (n'-1) = True
      pow' (False:ys)   _ !d2                         = pow ys d2
      pow' (True :ys)   _ !d2                         = pow ys $ (d2*a')`mod`n'
      pow' _            _   _                         = error "bad case"
  -- 
  toBinary 0 = []
  toBinary x = (testBit x 0) : (toBinary $ x `shiftR` 1)

modular_exponentiation :: Integer -> Integer -> Integer -> Integer
modular_exponentiation x y m = m_e_loop x y 1
 where
  m_e_loop _   0 !result = result
  m_e_loop !b !e !result = m_e_loop b' e' result'
   where
    !b'      = (b * b) `mod` m
    !e'      = e `shiftR` 1
    !result' = if testBit e 0 then (result * b) `mod` m else result

-- Compute the modular inverse (d = e^-1 mod phi) via the extended 
-- euclidean algorithm. And if you think I understand the math behind this,
-- I have a bridge to sell you.
modular_inverse :: Integer -> Integer -> Integer
modular_inverse e phi = x `mod` phi
 where
  (_, x, _) = gcde e phi

gcde :: Integer -> Integer -> (Integer, Integer, Integer)
gcde a b | d < 0     = (-d, -x, -y)
         | otherwise = (d, x, y)
 where
  (d, x, y) = gcd_f (a,1,0) (b,0,1)
  gcd_f (r1, x1, y1) (r2, x2, y2) 
    | r2 == 0   = (r1, x1, y1)
    | otherwise = let (q, r) = r1 `divMod` r2
                  in gcd_f (r2, x2, y2) (r, x1 - (q * x2), y1 - (q * y2))
