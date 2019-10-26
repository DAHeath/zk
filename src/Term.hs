{-# language LambdaCase #-}
{-# language FlexibleContexts #-}
{-# language RecordWildCards #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language TemplateHaskell #-}
{-# language DataKinds #-}
module Term where

import           Control.Lens hiding (Context)
import           Control.Monad.Except
import           Control.Monad.Fail
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Bits
import qualified Data.Map as Map
import           Data.Map (Map)
import qualified Data.Set as Set
import           Data.Set (Set)

type V = String

data Term
  -- base language
  = Let Pat Term Term
  | Anti String
  | Var V
  | Xor Term Term
  | And Term Term
  | Pair Term Term
  | Fst Term
  | Snd Term
  | Unit
  -- ring language extensions
  | Add Term Term
  | Mul Term Term
  | Negate Term
  | Construct Term
  | Project Term
  deriving (Show, Read, Eq, Ord)

data Pat
  = PVar V
  | PPair Pat Pat
  | PUnit
  deriving (Show, Read, Eq, Ord)

data Type
  = Boolean
  | Prod Type Type
  | One
  deriving (Show, Read, Eq, Ord)

data Value b r
  = VBoolean b
  | VRing r
  | VPair (Value b r) (Value b r)
  | VUnit
  deriving (Show, Read, Eq, Ord)

type Env b r = Map V (Value b r)

data EvalStrat m b r = EvalStrat
  { xorGate :: b -> b -> b
  , andGate :: b -> b -> m b
  , addGate :: r -> r -> r
  , negGate :: r -> r
  , mulGate :: r -> r -> m r
  , cnsGate :: [b] -> m r
  , prjGate :: r -> m [b]
  }

eval :: MonadFail m => EvalStrat m b r -> Term -> ReaderT (Env b r) m (Value b r)
eval EvalStrat{..} = go
  where
    go = \case
      Let p t0 t1 -> do
        v0 <- go t0
        bind p v0 (go t0)
      Var x -> asks (Map.! x)
      Xor t0 t1 -> do
        VBoolean b0 <- go t0
        VBoolean b1 <- go t1
        pure (VBoolean (xorGate b0 b1))
      And t0 t1 -> do
        VBoolean b0 <- go t0
        VBoolean b1 <- go t1
        lift (VBoolean <$> andGate b0 b1)
      Pair t0 t1 -> VPair <$> go t0 <*> go t1
      Fst t -> do VPair v _ <- go t ; pure v
      Snd t -> do VPair _ v <- go t ; pure v
      Unit -> pure VUnit
      Add t0 t1 -> do
        VRing r0 <- go t0
        VRing r1 <- go t1
        pure (VRing $ addGate r0 r1)
      Negate t -> do
        VRing r <- go t
        pure (VRing $ negGate r)
      Mul t0 t1 -> do
        VRing r0 <- go t0
        VRing r1 <- go t1
        lift (VRing <$> mulGate r0 r1)
      Construct t -> do
        v <- go t
        lift (VRing <$> (cnsGate =<< uncons v))
      Project t -> do
        VRing r <- go t
        lift (foldr (VPair . VBoolean) VUnit <$> prjGate r)

    bind :: (MonadFail m, MonadReader (Env b r) m) => Pat -> Value b r -> m a -> m a
    bind p v ac = do
      env <- ask
      env' <- go p v env
      local (const env') ac
      where
        go (PVar x) v env = pure (Map.insert x v env)
        go (PPair p0 p1) (VPair v0 v1) env = go p0 v0 =<< go p1 v1 env
        go PUnit VUnit env = pure env
        go _ _ _ = Control.Monad.Fail.fail "bad pattern binding"

    uncons :: MonadFail m => Value b r -> m [b]
    uncons VUnit = pure []
    uncons (VPair (VBoolean b) v) = (b:) <$> uncons v

cleartext :: Term -> ReaderT (Env Bool Mod) Maybe (Value Bool Mod)
cleartext = eval cleartextStrat

cleartextStrat :: EvalStrat Maybe Bool Mod
cleartextStrat = EvalStrat{..}
  where
    xorGate = xor
    andGate b0 b1 = pure (b0 && b1)
    addGate = (+)
    negGate = negate
    mulGate i j = pure (i * j)
    cnsGate bs = pure (sum (zipWith (*) (map bToZ bs) powsOf2))
      where bToZ b = if b then 1 else 0
    prjGate i = pure (map (unMod i `testBit`) [0..31])

powsOf2 :: [Mod]
powsOf2 = 1: map (2*) powsOf2

data BoolEnc
  = BoolSymbol String
  | BoolXor (Set BoolEnc)
  | BoolHash BoolEnc
  deriving (Show, Read, Eq, Ord)

encXor :: BoolEnc -> BoolEnc -> BoolEnc
encXor b0 b1 =
  let s = toSet b0 `interUnion` toSet b1
   in if length s == 1
         then Set.findMin s
         else BoolXor s
  where
    interUnion s0 s1 = Set.union s0 s1 `Set.difference` Set.intersection s0 s1
    toSet (BoolXor s) = s
    toSet b = Set.singleton b

hash :: BoolEnc -> BoolEnc
hash = BoolHash

data RingEnc
  = RingSymbol String
  | RingSum (Map RingEnc Mod)
  deriving (Show, Read, Eq, Ord)

ringAdd :: RingEnc -> RingEnc -> RingEnc
ringAdd r0 r1 = RingSum . Map.filter (/= 0) $ Map.unionWith (+) (toMap r0) (toMap r1)
  where
    toMap (RingSum m) = m
    toMap r = Map.singleton r 1

ringSub :: RingEnc -> RingEnc -> RingEnc
ringSub r0 r1 = RingSum . Map.filter (/= 0) $ Map.unionWith (-) (toMap r0) (toMap r1)
  where
    toMap (RingSum m) = m
    toMap r = Map.singleton r 1

ringZero :: RingEnc
ringZero = RingSum Map.empty

data KnownRing = KnownRing Mod RingEnc
  deriving (Show, Read, Eq, Ord)

knownAdd :: KnownRing -> KnownRing -> KnownRing
knownAdd (KnownRing l0 b0) (KnownRing l1 b1) = KnownRing (l0 + l1) (b0 `ringAdd` b1)

knownSub :: KnownRing -> KnownRing -> KnownRing
knownSub (KnownRing l0 b0) (KnownRing l1 b1) = KnownRing (l0 - l1) (b0 `ringSub` b1)

knownZero :: KnownRing
knownZero = KnownRing 0 ringZero

data KnownBool = KnownBool Bool BoolEnc
  deriving (Show, Read, Eq, Ord)

knownXor :: KnownBool -> KnownBool -> KnownBool
knownXor (KnownBool l0 b0) (KnownBool l1 b1) = KnownBool (l0 `xor` l1) (b0 `encXor` b1)

data VerifierState = VerifierState
  { _material :: [BoolEnc]
  , _delta :: BoolEnc
  } deriving (Show, Read, Eq, Ord)
makeLenses ''VerifierState

type ProverState = [BoolEnc]

newtype Prover a = Prover { runProver :: StateT ProverState Maybe a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadState ProverState)

newtype Verifier a = Verifier { runVerifier :: StateT VerifierState Maybe a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadState VerifierState)

prover :: Term -> ReaderT (Env KnownBool KnownRing) Prover (Value KnownBool KnownRing)
prover = eval EvalStrat{..}
  where
    xorGate = knownXor
    andGate = proverAnd
    addGate = knownAdd
    negGate = knownSub knownZero
    mulGate = undefined
    cnsGate = undefined
    prjGate = undefined

verifier :: Term -> ReaderT (Env BoolEnc RingEnc) Verifier (Value BoolEnc RingEnc)
verifier = eval EvalStrat{..}
  where
    xorGate = encXor
    andGate = verifierAnd
    addGate = ringAdd
    negGate = ringSub ringZero
    mulGate = undefined
    cnsGate = undefined
    prjGate = undefined

proverAnd :: KnownBool -> KnownBool -> Prover KnownBool
proverAnd (KnownBool la a) (KnownBool lb b) = do
  (row:rows) <- get
  put rows
  let ha = hash a
  let c = if la then row `encXor` ha `encXor` b else ha
  pure (KnownBool (la && lb) c)

verifierAnd :: BoolEnc -> BoolEnc -> Verifier BoolEnc
verifierAnd a b = do
  d <- use delta
  let c = hash a
  let row = hash (a `encXor` d) `encXor` b `encXor` c
  modify (material %~ (row:))
  pure c

verifierCons :: [BoolEnc] -> Verifier RingEnc
verifierCons = undefined

verifierProj :: RingEnc -> Verifier [BoolEnc]
verifierProj = undefined

proverMul :: RingEnc -> RingEnc -> Prover RingEnc
proverMul = undefined

verifierMul :: RingEnc -> RingEnc -> Prover RingEnc
verifierMul = undefined
