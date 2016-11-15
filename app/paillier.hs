import System.Random
import Primes

data PublicKey = Pub Integer Integer
    deriving Show
data PrivateKey = Priv Integer Integer
    deriving Show

keys :: RandomGen g => g -> Int -> (PublicKey, PrivateKey, g)
keys g sizeBits = (Pub n g2, Priv lambda mu, g')
    where
        kLen = fromIntegral $ sizeBits `div` 8
        (p, q, g') = generate_pq g kLen
        lambda = (p - 1) * (q - 1)
        n = p * q
        mu = modInverse lambda n
        g2 = n + 1

modInverse 1 _ = 1
modInverse x y = (n * y + 1) `div` x
    where n = x - modInverse (y `mod` x) x

modPow m = pow' (modMul m) (modSquare m)
    where
        modMul m a b = (a * b) `mod` m
        modSquare m a = (a * a) `rem` m
        pow' _ _ _ 0 = 1
        pow' m s x n = f x n 1
            where
                f x n y
                    | n == 1 = x `m` y
                    | r == 0 = f x2 q y
                    | otherwise = f x2 q (x `m` y)
                    where
                        (q, r) = quotRem n 2
                        x2 = s x

encrypt rg m (Pub n g) = (c, rg')
    where
        (r, rg') = large_random_prime rg 32
        n2 = n ^ 2
        x = (modPow n2 r n)
        c = ((modPow n2 g m) * x) `mod` n2

decrypt c (Pub n g) (Priv lambda mu) = p
    where
        n2 = n ^ 2
        x = modPow n2 c lambda - 1
        p = ((x `div` n) * mu) `mod` n

pAdd a b (Pub n g) = (a * b) `mod` (n ^ 2)
pAddPlain a b (Pub n g) = a * (modPow (n ^ 2) g b)
pMulPlain a b (Pub n g) = modPow (n ^ 2) a b

main = do
    g <- getStdGen

    let (pub, priv, g') = keys g 256

        m1 = 7
        m2 = 17
        (c1, g'') = encrypt g' m1 pub
        (c2, _) = encrypt g'' m2 pub

        r = pAdd c1 c2 pub
        r' = decrypt r pub priv

        s = pAddPlain c1 18 pub
        s' = decrypt s pub priv

        t = pMulPlain c1 3 pub
        t' = decrypt t pub priv

    putStrLn ((show m1) ++ " becomes " ++ (show c1))
    putStrLn ((show m2) ++ " becomes " ++ (show c2))

    putStrLn ((show m1) ++ " + " ++ (show m2) ++ " = " ++ (show r'))
    putStrLn ((show m1) ++ " + 18 = " ++ (show s'))
    putStrLn ((show m1) ++ " * 3 = " ++ (show t'))
