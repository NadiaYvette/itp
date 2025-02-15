\documentclass{article}
%include polycode.fmt
%format ^ = "^"
%format pow (x) (y) = "{" x "}^{" y "}"
%format powPar (x) (y) = "{\left(" x "\right)}^{" y "}"
%format fpow (x) (y) = "{" x "}^{" y "}"
%format fpowPar (x) (y) = "{\left(" x "\right)}^{" y "}"
%format frac (x) (y) = "\frac{" x "}{" y "}"
%format logBase (x) (y) = "{\log_{" x "}{" y "}}"
%format * = "\cdot"
%format abs (x) = "\mathopen{\vert}" x "\mathclose{\vert}"
%format ceiling (x) = "\mathopen{\lceil}" x "\mathclose{\rceil}"
%format Bool = "{\mathbb{B}}"
%format fromInteger = "{\iota_{\mathbb{Z}\mapsto\mathbb{R}}}"
%format Integer = "{\mathbb{Z}}"
%format Natural = "{\mathbb{N}}"
%format delta = "\delta"
%format epsilon = "\varepsilon"
%format forall = "{\forall}"
%format kappa_1 = "{\kappa_1}"
%format kappa_2 = "{\kappa_2}"
%format sigma = "\sigma"
%format sigma_a = "\sigma_{a_k}"
%format sigma_b = "\sigma_{b_k}"
%format n_half = "{n_\frac{1}{2}}"
%format n_max = "{n_{\tt max}}"
%format x_half = "{x_\frac{1}{2}}"
%format x_f = "{x_f}"
%format x_t = "{x_t}"
%format x_ITP = "{x_{\tt ITP}}"
%format f_ITP = "{f(x_{\tt ITP})}"
%format f_a = "{f(a_k)}"
%format f_b = "{f(b_k)}"
%format n_0 = "{n_0}"
%format fx = "{f(x_n)}"
%format f'x = "{f'(x_n)}"
%format f''x = "{f''(x_n)}"
\usepackage{comment}
\begin{document}
%if False
\begin{code}
module Numeric.ITP (itp) where
import                          Control.Monad
import           "transformers" Control.Monad.Trans.RWS
\end{code}
%endif

\begin{code}
data ITP t = ITP
  { a, b, f_a, f_b, x_t, x_half, delta :: t
  , sigma :: Ordering
  , k :: Integer
  } deriving (Eq, Read, Show)

data ITPEnv t = ITPEnv
  { epsilon, kappa_1, kappa_2 :: t
  , f :: t -> t
  , sigma_a, sigma_b :: Ordering
  , n_0 :: Integer
  }
\end{code}

%if False
\begin{code}
{-# ANN itp ("HLint: ignore Redundant multi-way if" :: String) #-}
\end{code}
%endif
\begin{code}
itp :: forall m t . (Monad m, Ord t, RealFloat t, Show t)
  => RWST (ITPEnv t) () (ITP t) m ()
itp = do
  ITPEnv {..} <- ask
  ITP {..} <- get
  modify \s -> s { k = 0 }
  let n_half :: Integer = ceiling (logBase 2 (frac (b - a) (2 * epsilon)))
      n_max  :: Integer = n_half + n_0
      loop :: RWST (ITPEnv t) () (ITP t) m Bool
      loop = do
\end{code}
        Calculating parameters
\begin{spec}
        x_half <- gets x_half
\end{spec}
\begin{code}
        ITP {..} <- get
        modify \s -> s { x_half = frac (a + b) 2 }
        ITP {..} <- get
        let r = epsilon * fromInteger (pow 2 (n_max - k)) - frac (b - a) 2
        modify \s -> s { delta = kappa_1 * fpowPar (b - a) kappa_2 }
\end{code}
\begin{spec}
        delta <- gets delta
\end{spec}
\begin{code}
        ITP {..} <- get
\end{code}
        Interpolation
\begin{code}
        let x_f = frac (f_b * a - f_a * b) (f_b - f_a)
\end{code}
        Truncation
\begin{code}
        modify \s -> s { sigma = (x_half - x_f) `compare` 0 }
\end{code}
%if False
\begin{spec}
        sigma <- gets sigma
\end{spec}
%endif
\begin{code}
        ITP {..} <- get
        if  | delta <= abs (x_half - x_f)
            -> modify \s -> s { x_t = x_f + sgn sigma * delta }
            | otherwise
            -> modify \s -> s { x_t = x_half }
\end{code}
%if False
\begin{spec}
        x_t <- gets x_t
\end{spec}
%endif
\begin{code}
        ITP {..} <- get
\end{code}
        Projection
\begin{code}
        let x_ITP | abs (x_t - x_half) <= r
                  = x_t
                  | otherwise
                  = x_half - sgn sigma * r
\end{code}
        Updating Interval
\begin{code}
            f_ITP = f x_ITP
        case f_ITP `compare` 0 of
          EQ -> modify \s -> s { a = x_ITP, f_a = f_ITP
                               , b = x_ITP, f_b = f_ITP }
          o  | o == sigma_a
             -> modify \s -> s { a = x_ITP, f_a = f_ITP }
             | o == sigma_b
             -> modify \s -> s { b = x_ITP, f_b = f_ITP }
          _ -> error "error"
        modify \s -> s { k = k + 1 }
\end{code}
%if False
\begin{spec}
        k <- gets k
\end{spec}
%endif
\begin{code}
        ITP {..} <- get
        pure $ (b - a) > 2 * epsilon && k < n_max
  while loop
\end{code}

%if False
\begin{code}
frac :: Fractional t => t -> t -> t
frac x y = x / y

pow :: Num t => t -> Integer -> t
pow x y = x ^ y

fpow, fpowPar :: Floating t => t -> t -> t
fpow x y = x ** y
fpowPar = fpow

sgn :: Num t => Ordering -> t
sgn = \case
  LT -> -1
  EQ ->  0
  GT ->  1

while :: forall m' . Monad m' => m' Bool -> m' ()
while m = go where
  go = do
    b <- m
    when b do go
\end{code}
%endif
\end{document}
