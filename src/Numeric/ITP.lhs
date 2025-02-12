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

{-# ANN itp ("HLint: ignore Redundant multi-way if" :: String) #-}
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
        -- Interpolation
        let x_f = (f_b * a - f_a * b) / (f_b - f_a)
        -- Truncation
        modify \s -> s { sigma = (x_half - x_f) `compare` 0 }
        -- sigma <- gets sigma
        ITP {..} <- get
        if  | delta <= abs (x_half - x_f)
            -> modify \s -> s { x_t = x_f + sgn sigma * delta }
            | otherwise
            -> modify \s -> s { x_t = x_half }
        -- x_t <- gets x_t
        ITP {..} <- get
        -- Projection
        let x_ITP | abs (x_t - x_half) <= r
                  = x_t
                  | otherwise
                  = x_half - sgn sigma * r
        -- Updating Interval
            f_ITP = f x_ITP
        case f_ITP `compare` 0 of
          EQ -> modify \s -> s { a = x_ITP, f_a = f_ITP
                               , b = x_ITP, f_b = f_ITP }
          o  | o == sigma_a
             -> modify \s -> s { a = x_ITP, f_a = f_ITP }
             | o == sigma_b
             -> modify \s -> s { b = x_ITP, f_b = f_ITP }
          _ -> error "error"
        modify \s -> s { j = j + 1 }
        -- j <- gets j
        ITP {..} <- get
        pure $ (b - a) > 2 * epsilon && j < n_max
  while loop
\end{code}
\end{document}
