{-# LANGUAGE PartialTypeSignatures
           , FlexibleContexts

 #-}
--            , AllowAmbiguousTypes
import Control.Monad.Random.Class
import Primes

import Control.Monad.State --(State, evalState, get, put, state, lift)
import System.Random -- (StdGen, mkStdGen, random)
import Control.Applicative ((<$>))
import Control.Monad.Reader
import Control.Monad.Reader.Class

data PublicKey a = Pub {n :: Integer,  g :: Integer}
    deriving Show
data PrivateKey a = Priv {lambda :: Integer, mu :: Integer}
    deriving Show

data SecInt = Sec Integer

instance Monoid SecInt where
    mempty  = undefined
    mappend = undefined

instance Show SecInt where
   show (Sec i) = "Sec" ++ show i

type RandEnv a = State StdGen a
type PubKeyEnv a = Reader (PublicKey a)

runRandom :: RandEnv a -> Int -> a
runRandom action seed = evalState action $ mkStdGen seed

keys'' :: (MonadState (StdGen) m) =>
          Int -> m (PublicKey a, PrivateKey b)
keys'' sizeBits = do
    g <- get
    let kLen = fromIntegral $ sizeBits `div` 8
    let (p, q, g') = generate_pq g kLen
    let lambda = (p - 1) * (q - 1)
    let n = p * q
    let mu = modInverse lambda n
    let g2 = n + 1
    put g'
    return $ (Pub n g2, Priv lambda mu)

keys :: RandomGen g => 
        g -> Int -> (PublicKey a, PrivateKey b, g)
keys g sizeBits = (Pub n g2, Priv lambda mu, g')
    where
        kLen = fromIntegral $ sizeBits `div` 8
        (p, q, g') = generate_pq g kLen
        lambda = (p - 1) * (q - 1)
        n = p * q
        mu = modInverse lambda n
        g2 = n + 1

encrypt'' :: (MonadReader (PublicKey a) m, MonadState (StdGen) m) =>
             Integer -> m SecInt
encrypt'' i = do
    (Pub n g) <- ask
    rg <- get
    let (r, rg') = large_random_prime rg 32
    let n2 = n ^ 2
    let x = (modPow n2 r n)
    let c = Sec $ ((modPow n2 g i) * x) `mod` n2
    put rg'
    return c

encrypt' :: RandomGen t =>
            t -> Integer -> (PubKeyEnv a) (SecInt, t)
encrypt' rg m = do
    (Pub n g) <- ask
    let (r, rg') = large_random_prime rg 32
    let n2 = n ^ 2
    let x = (modPow n2 r n)
    let c = Sec $ ((modPow n2 g m) * x) `mod` n2
    return (c, rg')

decrypt' :: SecInt -> PrivateKey t1 -> (PubKeyEnv a) Integer
decrypt' (Sec c) (Priv lambda mu) = do
    n <- asks n
    let x = modPow (n * n) c lambda - 1
    let p = ((x `div` n) * mu) `mod` n
    return p

pAdd' :: SecInt -> SecInt -> (PubKeyEnv a) SecInt
pAdd' (Sec a) (Sec b) = do
    n <- asks n
    return $ Sec $ (a * b) `mod` (n ^ 2) 

pAddPlain :: SecInt -> Integer -> PublicKey t -> SecInt
pAddPlain (Sec a) b (Pub n g) = Sec $ a * (modPow (n ^ 2) g b)

pMulPlain :: SecInt -> Integer -> PublicKey t -> SecInt
pMulPlain (Sec a) b (Pub n g) = Sec $ modPow (n ^ 2) a b

data MyContext = MyContext
  { foo :: String
  , bar :: Int
  } deriving (Show)

computation :: (MonadReader MyContext m) => Int -> m (Maybe String)
--computation :: Int -> Reader MyContext (Maybe String) 
computation i = do
  n <- asks bar
  x <- asks foo
  if n > i
    then return (Just x)
    else return Nothing

ex1 :: Maybe String
ex1 = runReader  (computation 0) (MyContext "hello" 1)

ex2 :: Maybe String
ex2 = runReader  (computation 1) (MyContext "haskell" 0)

main :: IO ()
main = do

    liftIO $ putStrLn $ show ex1
    liftIO $ putStrLn $ show ex2

    g <- getStdGen

    let (pub2, priv2) = runState (keys'' 256) g

    let (pub, priv, g') = keys g 256
        m1 = 7
        m2 = 17
        -- c0 = runReaderT (runStateT (encrypt'' m1) g) pub2
        (c1, g'') = runReader (encrypt' g' m1) pub
        (c2, _) = runReader (encrypt' g'' m2) pub
        r = runReader (pAdd' c1 c2) pub
        r'' = runReader (decrypt' r priv) pub

        -- s = pAddPlain c1 18 pub
        -- s' = decrypt s pub priv

        -- t = pMulPlain c1 3 pub
        -- t' = decrypt t pub priv

    putStrLn $ (show m1) ++ " becomes " ++ (show c1)
    putStrLn $ (show m2) ++ " becomes " ++ (show c2)
    putStrLn $ "Their sum is: " ++ (show r)

    putStrLn $ (show m1) ++ " + " ++ (show m2) ++ " = " ++ (show r'')
    -- putStrLn ((show m1) ++ " + 18 = " ++ (show s'))
    -- putStrLn ((show m1) ++ " * 3 = " ++ (show t'))
