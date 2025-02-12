\documentclass{article}
%include polycode.fmt
%format ^ = "^"
%format * = "\cdot"
%format Poly.deriv = "\frac{d}{dx}"
%format fx = "{f(x_n)}"
%format f'x = "{f'(x_n)}"
%format f''x = "{f''(x_n)}"
\usepackage{comment}
\begin{document}
\documentclass{article}
%include polycode.fmt
%format ^ = "^"
%format * = "\cdot"
%format Poly.deriv = "\frac{d}{dx}"
%format fx = "{f(x_n)}"
%format f'x = "{f'(x_n)}"
%format f''x = "{f''(x_n)}"
\usepackage{comment}
\begin{document}
\begin{code}
module Numeric.ITP where
import                          Control.Monad
import                          Control.Monad.Trans
import           "transformers" Control.Monad.Trans.RWS
\end{code}

\begin{code}
data ITP t = ITP
  { a, b, f_a, f_b, x_t, x_half, delta :: t
  , sigma :: Ordering
  , j :: Integer
  } deriving (Eq, Read, Show)

data ITPEnv t = ITPEnv
  { epsilon, kappa_1, kappa_2 :: t
  , f :: t -> t
  , sigma_a, sigma_b :: Ordering
  , n_0 :: Integer
  }

-- itp :: forall m t . ()
  -- => Num t
  -- => MonadReader m
  -- => EnvType m ~ ReaderT (ITPEnv t) m ()
  -- => MonadState m
  -- => StateType m ~ StateT (ITP t) m ()
  -- => m ()
itp :: forall m t . ()
  => Monad m -- m ~ ST s
  => MonadIO m
  => Floating t
  => Fractional t
  => Num t
  => Ord t
  => RealFrac t
  => Show t
  => RWST (ITPEnv t) [ITP t] (ITP t) m ()
itp = do
  ITPEnv {..} <- ask
  ITP {..} <- get
  modify \s -> s { j = 0 }
  let n_half :: Integer = ceiling . logBase 2 $ (b - a) / (2 * epsilon)
      n_max  :: Integer = n_half + n_0
      sgn :: Ordering -> t = \case
        LT -> -1
        EQ ->  0
        GT ->  1
      while :: forall m' . Monad m' => m' Bool -> m' ()
      while m = go where
        go = do
          b <- m
          when b do go
      loop :: RWST (ITPEnv t) [ITP t] (ITP t) m Bool
      loop = do
        -- Calculating parameters
        -- itp <- get
        -- tell [itp]
        -- x_half <- gets x_half
        ITP {..} <- get
        modify \s -> s { x_half = (a + b) / 2 }
        ITP {..} <- get
        let r = epsilon * fromInteger (2 ^ (n_max - j)) - (b - a) / 2
        modify \s -> s { delta = kappa_1 * (b - a) ** kappa_2 }
        -- delta <- gets delta
        ITP {..} <- get
        -- liftIO . putStrLn $ "delta = " <> show delta
        -- Interpolation
        let x_f = (f_b * a - f_a * b) / (f_b - f_a)
        -- Truncation
        modify \s -> s { sigma = (x_half - x_f) `compare` 0 }
        -- sigma <- gets sigma
        ITP {..} <- get
        -- liftIO $ print (LT, x_f + sgn sigma * delta, x_half)
        {- liftIO . putStr $ unlines
          [ "x_half = " <> show x_half
          , "x_f = " <> show x_f
          , "x_t | delta <= abs (x_half - x_f) = "
          , "    = " <> show (x_f + sgn sigma * delta)
          , "    | otherwise"
          , "    = " <> show x_half ] -}
        -- liftIO $ print (LT, delta, abs (x_half - x_f), sigma)
        {- liftIO . putStr $ unlines
          [ "delta = " <> show delta
          , "abs (x_half - x_f) = " <> show (abs (x_half - x_f))
          , "sigma = " <> show sigma
          , "if  | " <> show delta <> " <= " <> show (abs (x_half - x_f))
          , "    -> x_t = " <> show (x_f + sgn sigma * delta)
          , "    | otherwise"
          , "    -> x_t = " <> show x_half ] -}
        {-# HLINT ignore "Redundant multi-way if" #-}
        if  | delta <= abs (x_half - x_f)
            -> do modify \s -> s { x_t = x_f + sgn sigma * delta }
                  -- liftIO $ putStrLn "secant branch"
            | otherwise
            -> do modify \s -> s { x_t = x_half }
                  -- liftIO $ putStrLn "bisect branch"
        -- x_t <- gets x_t
        ITP {..} <- get
        -- liftIO . putStrLn $ "x_t = " <> show x_t
        -- Projection
        -- liftIO $ print (LT, r, abs (x_t - x_half))
        let x_ITP | abs (x_t - x_half) <= r
                  = x_t
                  | otherwise
                  = x_half - sgn sigma * r
        -- Updating Interval
            f_ITP = f x_ITP
        -- liftIO $ print (EQ, x_t, x_half, x_half - sgn sigma, x_ITP, f_ITP)
        case f_ITP `compare` 0 of
          EQ -> do modify \s -> s { a = x_ITP, f_a = f_ITP
                                  , b = x_ITP, f_b = f_ITP }
                   -- liftIO . putStrLn $ "f_ITP == " <> show f_ITP <> " " <> show EQ
          o  | o == sigma_a
             -> do modify \s -> s { a = x_ITP, f_a = f_ITP }
                   -- liftIO . putStrLn $ "f_ITP == " <> show f_ITP <> " " <> show o
             | o == sigma_b
             -> do modify \s -> s { b = x_ITP, f_b = f_ITP }
                   -- liftIO . putStrLn $ "f_ITP == " <> show f_ITP <> " " <> show o
          _ -> error "error"
        modify \s -> s { j = j + 1 }
        -- j <- gets j
        ITP {..} <- get
        {- liftIO . putStr $ unlines
          [ "b - a = " <> show (b - a)
          , "2 * epsilon = " <> show (2 * epsilon)
          , "j = " <> show j
          , "n_max = " <> show n_max ] -}
        pure $ (b - a) > 2 * epsilon && j < n_max
  while loop
\end{code}
\end{document}
