{-# LANGUAGE
            FlexibleInstances
        ,   FlexibleContexts
        ,   UndecidableInstances
        ,   IncoherentInstances 
 #-}

import Primes
import Control.Monad.State 
import System.Random 
import Control.Monad.Random.Class
import Control.Applicative ((<$>))
import Control.Monad.Reader
import Control.Monad.Reader.Class
import Data.Semigroup
import Data.List.NonEmpty
import Debug.Trace
import GHC.Show

import qualified Data.ByteString as B 
import qualified Data.ByteString.Base64 as B64
import qualified Data.ByteString.Base16 as B16
import qualified Data.ByteString.Char8 as BC 
import Data.Word
import Data.Bits
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))

integer2Bytes::Integer->[Word8]
integer2Bytes 0 = []
integer2Bytes x = integer2Bytes (x `shiftR` 8) ++ [fromInteger (x .&. 255)]

debug = flip trace

data PublicKey = Pub {n :: Integer,  g :: Integer}
    deriving Show
data PrivateKey = Priv {lambda :: Integer, mu :: Integer}
    deriving Show

data SecInt = Sec Integer
data SecInt' = Sec' Integer PublicKey

class (MonadReader PublicKey m) => m (HES a) where
  (<>) :: m a -> m a -> m a

instance Show SecInt where
   show (Sec i) = (BC.unpack $ B16.encode $ B.pack $ integer2Bytes $ fromIntegral i)

-- decryptShow :: (MonadReader PublicKey m) => 
--                SecInt -> PrivateKey -> m String
-- decryptShow si priv = do
--    return $ (show si) ++ " = " ++ (show $ decrypt'' si priv)

liftM2'  :: (MonadReader PublicKey m) => (a1 -> a2 -> r) -> m a1 -> m a2 -> m r
liftM2' f m1 m2          = do { x1 <- m1; x2 <- m2; return (f x1 x2) }

instance (MonadReader PublicKey m) => Semigroup (m SecInt) where
     (<>) a b = do
            Sec x <- a
            Sec y <- b
            z <- asks n
            return $ Sec $ (x * y)  `mod` (z ^ 2)

type RandEnv a = State StdGen a
type PubKeyEnv = Reader (PublicKey)

runRandom :: RandEnv a -> Int -> a
runRandom action seed = evalState action $ mkStdGen seed

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

keysM :: (MonadState (StdGen) m) =>
          Int -> m (PublicKey, PrivateKey)
keysM sizeBits = do
    g <- get
    let (pub, priv, g') = keys g sizeBits
    put g'
    return $ (pub, priv)

encrypt :: RandomGen t =>
           t -> Integer -> (PubKeyEnv) (SecInt, t)
encrypt rg m = do
    (Pub n g) <- ask
    let (r, rg') = large_random_prime rg 32
    let n2 = n ^ 2
    let x = (modPow n2 r n)
    let c = Sec $ ((modPow n2 g m) * x) `mod` n2
    return (c, rg')

encryptM :: (MonadReader (PublicKey) m, MonadState (StdGen) m) =>
             Integer -> m SecInt
encryptM i = do
    (Pub n g) <- ask
    rg <- get
    let (r, rg') = large_random_prime rg 32
    let n2 = n ^ 2
    let x = (modPow n2 r n)
    let c = Sec $ ((modPow n2 g i) * x) `mod` n2
    put rg'
    return $ c

decryptM :: (MonadReader PublicKey m) =>
            SecInt -> PrivateKey -> m Integer
decryptM (Sec c) (Priv lambda mu) = do
    n <- asks n
    let x = modPow (n * n) c lambda - 1
    let p = ((x `div` n) * mu) `mod` n
    return p

pAdd :: SecInt -> SecInt -> (PubKeyEnv) SecInt
pAdd (Sec a) (Sec b) = do
    n <- asks n
    return $ Sec $ (a * b) `mod` (n ^ 2) 

pAddM :: (MonadReader PublicKey m) =>
         SecInt -> SecInt -> m SecInt
pAddM (Sec a) (Sec b) = do
    n <- asks n
    return $ Sec $ (a * b) `mod` (n ^ 2)     

-- if we can derive foldl1 from Semigroup
-- but we could also just treat 0 as (Sec 0) and
-- have guard on Sec 0 for special addition
-- this way we'd get a Monoid
pAddM' :: (MonadReader PublicKey m) =>
           m SecInt -> m SecInt -> m SecInt
pAddM' a b = do
    n <- asks n
    return $ Sec $ (1 * 2) `mod` (n ^ 2)

pAddMl :: (MonadReader PublicKey m) =>
           m SecInt -> SecInt -> m SecInt
pAddMl a (Sec b) = do
    nn <- asks n
    aa <- ((*) b) <$> (f <$> a)
    return $ Sec $ aa `mod` (nn ^ 2) 
      where
    f :: SecInt -> Integer 
    f (Sec a) = a 

----------------------------------

pAddPlain :: SecInt -> Integer -> PublicKey -> SecInt
pAddPlain (Sec a) b (Pub n g) = Sec $ a * (modPow (n ^ 2) g b)

pMulPlain :: SecInt -> Integer -> PublicKey -> SecInt
pMulPlain (Sec a) b (Pub n g) = Sec $ modPow (n ^ 2) a b

----------------------------------

m1 = 7
m2 = 17
ms = [1,2,3]

mainEnv :: IO ()
mainEnv = do

    g <- getStdGen

    let (pub, priv, g') = keys g 256
 
    let q = flip runReader pub $ do
                (c1, g'') <- encrypt g' m1
                (c2, _) <- encrypt g'' m2
                toRet <- pAdd c1 c2 
                return $ toRet

        (c1, g'') = runReader (encrypt g' m1) pub
        (c2, _) = runReader (encrypt g'' m2) pub

        r = runReader (pAdd c1 c2) pub :: SecInt
        r'' = runReader (decryptM r priv) pub :: Integer

    putStrLn $ (show m1) ++ " becomes " ++ (show c1)
    putStrLn $ (show m2) ++ " becomes " ++ (show c2)
    putStrLn $ "Their sum is: " ++ (show r) ++ " = " ++ (show r'')

mainMonad :: IO ()
mainMonad = do

    g <- getStdGen

    let ((pub, priv), g') = runState (keysM 256) g

    _ <- flip runReaderT pub $ do 

          (c1, c2) <- flip evalStateT g' $ do
            c1 <- encryptM m1
            c2 <- encryptM m2
            return (c1, c2)

          r <- pAddM c1 c2 

          liftIO $ putStrLn $ (show m1) ++ " becomes " ++ (show c1)
          liftIO $ putStrLn $ (show m2) ++ " becomes " ++ (show c2)
          
          r'' <- decryptM r priv
          
          liftIO $ putStrLn $ "\nTheir sum is: " ++ (show r) ++ " = " ++ (show r'')
         
          let ms' = Prelude.take 999 $ [1..]

          (l, l0) <- flip evalStateT g' $ do
            l <- sequence $ encryptM <$> ms' 
            l0 <- encryptM 0
            return $ (l, l0)

          es <- foldl pAddMl (pure l0) l 
          des <- decryptM es priv
          liftIO $ putStrLn $ "\ntake " ++ (show $ Prelude.length ms') ++ " [1..]" 
          liftIO $ putStrLn $ "\nThe (foldl) sum is: " ++ (show es) ++ " = " ++ (show des)
         
          ll <- flip evalStateT g' $ do
            toRet <- sequence $ encryptM <$> fromList ms'
            return toRet
       
          es' <- sconcat (pure <$> ll) 
          des' <- decryptM es' priv
          liftIO $ putStrLn $ "\nThe (sconcat) sum is: " ++ (show es') ++ " = " ++ (show des')
          
          return () 

    return ()

main :: IO ()
main = mainMonad
