{-# LANGUAGE
            FlexibleInstances
        ,   FlexibleContexts
        ,   UndecidableInstances
        ,   IncoherentInstances 
 #-}

   --      ,   DeriveAnyClass
     --             ,   DeriveFoldable
 -- ,PartialTypeSignatures
 -- , FlexibleContexts
            --, FlexibleInstances
           --, UndecidableInstances
--            , AllowAmbiguousTypes
--            , NoImplicitPrelude
--
-- import Protolude hiding (show)
import Primes
import Control.Monad.State --(State, evalState, get, put, state, lift)
import System.Random -- (StdGen, mkStdGen, random)
import Control.Monad.Random.Class
import Control.Applicative ((<$>))
import Control.Monad.Reader
import Control.Monad.Reader.Class
import Data.Semigroup
import Debug.Trace
import GHC.Show

import qualified Data.ByteString as B
import qualified Data.ByteString.Base64 as B64
import qualified Data.ByteString.Base16 as B16
import qualified Data.ByteString.Char8 as BC
import Data.Word
import Data.Bits
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

integer2Bytes::Integer->[Word8]
integer2Bytes 0 = []
integer2Bytes x = integer2Bytes (x `shiftR` 8) ++ [fromInteger (x .&. 255)]

debug = flip trace

data PublicKey = Pub {n :: Integer,  g :: Integer}
    deriving Show
data PrivateKey = Priv {lambda :: Integer, mu :: Integer}
    deriving Show

-- Foldable expects kind ‘* -> *’, but ‘m SecInt’ has kind ‘*’
data SecInt = Sec Integer -- deriving (Num)

data SecInt' = Sec' Integer PublicKey

instance Show SecInt where
   show (Sec i) = (BC.unpack $ B16.encode $ B.pack $ integer2Bytes $ fromIntegral i)

-- decryptShow :: (MonadReader PublicKey m) => 
--                SecInt -> PrivateKey -> m String
-- decryptShow si priv = do
--    return $ (show si) ++ " = " ++ (show $ decrypt'' si priv)

liftM2'  :: (MonadReader PublicKey m) => (a1 -> a2 -> r) -> m a1 -> m a2 -> m r
liftM2' f m1 m2          = do { x1 <- m1; x2 <- m2; return (f x1 x2) }

-- instance (MonadReader PublicKey m) => Monoid (m SecInt) where
--      mempty = return $ Sec 0 
--      mappend a b = do
--             Sec x <- a
--             Sec y <- b
--             z <- asks n
--             return $ Sec $ (x * y)  `mod` (z ^ 2)

-- instance (MonadReader PublicKey m, Monoid (m SecInt)) => Foldable m where
--     foldMap f empty = mempty
--     foldMap f a = undefined 

mysum (x:xs) = x `mappend` (mysum xs) 
mysum []     = mempty

--instance (MonadReader PublicKey m) => Foldable (m SecInt) where
    -- foldMap :: Monoid m => (a -> m) -> t a -> m
  --   foldMap = undefined

type RandEnv a = State StdGen a
type PubKeyEnv = Reader (PublicKey)

runRandom :: RandEnv a -> Int -> a
runRandom action seed = evalState action $ mkStdGen seed

keys'' :: (MonadState (StdGen) m) =>
          Int -> m (PublicKey, PrivateKey)
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
        g -> Int -> (PublicKey, PrivateKey, g)
keys g sizeBits = (Pub n g2, Priv lambda mu, g')
    where
        kLen = fromIntegral $ sizeBits `div` 8
        (p, q, g') = generate_pq g kLen
        lambda = (p - 1) * (q - 1)
        n = p * q
        mu = modInverse lambda n
        g2 = n + 1

encrypt'' :: (MonadReader (PublicKey) m, MonadState (StdGen) m) =>
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
            t -> Integer -> (PubKeyEnv) (SecInt, t)
encrypt' rg m = do
    (Pub n g) <- ask
    let (r, rg') = large_random_prime rg 32
    let n2 = n ^ 2
    let x = (modPow n2 r n)
    let c = Sec $ ((modPow n2 g m) * x) `mod` n2
    return (c, rg')

decrypt' :: SecInt -> PrivateKey -> (PubKeyEnv) Integer
decrypt' (Sec c) (Priv lambda mu) = do
    n <- asks n
    let x = modPow (n * n) c lambda - 1
    let p = ((x `div` n) * mu) `mod` n
    return p

decrypt'' :: (MonadReader PublicKey m) =>
             SecInt -> PrivateKey -> m Integer
decrypt'' (Sec c) (Priv lambda mu) = do
    n <- asks n
    let x = modPow (n * n) c lambda - 1
    let p = ((x `div` n) * mu) `mod` n
    return p

pAdd'''' :: (MonadReader PublicKey m) =>
           m SecInt -> m SecInt -> m SecInt
pAdd'''' a b = do
    n <- asks n
    return $ Sec $ (1 * 2) `mod` (n ^ 2)

pAdd''' :: (MonadReader PublicKey m) =>
           m SecInt -> SecInt -> m SecInt
pAdd''' a (Sec b) = do
    nn <- asks n
    aa <- ((*) b) <$> (f <$> a)
    return $ Sec $ aa `mod` (nn ^ 2) 
      where
    f :: SecInt -> Integer 
    f (Sec a) = a 

pAdd'' :: (MonadReader PublicKey m) =>
          SecInt -> SecInt -> m SecInt
pAdd'' (Sec a) (Sec b) = do
    n <- asks n
    return $ Sec $ (a * b) `mod` (n ^ 2)     

pAdd' :: SecInt -> SecInt -> (PubKeyEnv) SecInt
pAdd' (Sec a) (Sec b) = do
    n <- asks n
    return $ Sec $ (a * b) `mod` (n ^ 2) 

pAddPlain :: SecInt -> Integer -> PublicKey -> SecInt
pAddPlain (Sec a) b (Pub n g) = Sec $ a * (modPow (n ^ 2) g b)

pMulPlain :: SecInt -> Integer -> PublicKey -> SecInt
pMulPlain (Sec a) b (Pub n g) = Sec $ modPow (n ^ 2) a b

----------------------------------

m1 = 7
m2 = 17

ms = [1,2,3]

-- mainPlain :: IO ()
-- mainPlain = do
--     
--     putStrLn $ (show m1) ++ " becomes " ++ (show c1)
--     putStrLn $ (show m2) ++ " becomes " ++ (show c2)
--     putStrLn $ "Their sum is: " ++ (show r) ++ " = " ++ (show r'')

mainEnv :: IO ()
mainEnv = do

    g <- getStdGen

    let (pub, priv, g') = keys g 256
 
    --  q :: PubKeyEnv SecInt
    let q = flip runReader pub $ do
                (c1, g'') <- encrypt' g' m1
                (c2, _) <- encrypt' g'' m2
                toRet <- pAdd' c1 c2 
                return $ toRet

        (c1, g'') = runReader (encrypt' g' m1) pub
        (c2, _) = runReader (encrypt' g'' m2) pub

        r = runReader (pAdd' c1 c2) pub :: SecInt
        r'' = runReader (decrypt' r priv) pub :: Integer

    putStrLn $ (show m1) ++ " becomes " ++ (show c1)
    putStrLn $ (show m2) ++ " becomes " ++ (show c2)
    putStrLn $ "Their sum is: " ++ (show r) ++ " = " ++ (show r'')

mainMonad :: IO ()
mainMonad = do

    g <- getStdGen
    _ <- flip evalStateT g $ do
      (pub, priv) <- keys'' 256
      flip runReaderT pub $ do    
          c1 <- encrypt'' m1
          c2 <- encrypt'' m2
          r <- pAdd'' c1 c2 
          
          liftIO $ putStrLn $ (show m1) ++ " becomes " ++ (show c1)
          liftIO $ putStrLn $ (show m2) ++ " becomes " ++ (show c2)
          
          r'' <- decrypt'' r priv
          
          liftIO $ putStrLn $ "Their sum is: " ++ (show r) ++ " = " ++ (show r'')
         
          l <- sequence $ encrypt'' <$> [7, 17]
          let ll = [c1, c2]
          es <- foldl (pAdd''') (encrypt'' 0) l
          des <- decrypt'' es priv
          es' <- foldl (pAdd''') (encrypt'' 0) (r : ll) 
          des' <- decrypt'' es' priv

          liftIO $ putStrLn $ "es is: " ++ (show es) ++ " = " ++ (show des)
          liftIO $ putStrLn $ "es' is: " ++ (show es') ++ " = " ++ (show des')
          --ems <- ((encrypt'' 1) `mappend` (encrypt'' 2)) `mappend` (encrypt'' 3)
          --ems2 <- mysum $ encrypt'' <$> [1, 2]
          return () 

    return ()

main :: IO ()
main = mainMonad
