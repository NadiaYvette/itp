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
\usepackage{amsmath}
\usepackage[backend=bibtex]{biblatex}
\usepackage{comment}
\usepackage{url}
\addbibresource{argyros.bib}
\addbibresource{brent.bib}
\addbibresource{itp.bib}
\addbibresource{oliv.bib}
\addbibresource{sikorski.bib}
\begin{document}
\author{Nadia Chambers}
\title{Oliveira-Takahashi-Northrop ITP in Haskell}
\maketitle
\section{Introduction}
%if False
\begin{code}
module Numeric.ITP (itp) where
import                          Control.Monad
import           "transformers" Control.Monad.Trans.RWS
\end{code}
%endif

This implements the algorithm from \cite{oliv:taka:itp}, which has a
reference R implementation in \cite{itp}, which represents an improvement
over \cite{brent:71}, whose use of inverse quadratic interpolation is
somewhat idiosyncratic. It applies some of the ideas of \cite{argyros:19}
to the secant method. The methods account for Sikorski's observations in
\cite{sikorski:82}.
\subsection{Parameters}
The algorithm's parameters consist of an interval width bound to achieve
|epsilon|, two parameters related to the rate $\mu$ and order $q$ of
convergence, |kappa_1| and |kappa_2|, the function |f|, the signs of the
function at the two ends of the beginning interval, |sigma_a| and
|sigma_b|, and a boost to the calculated iteration limit |n_0|.
\begin{code}
data ITPEnv t = ITPEnv
  { epsilon, kappa_1, kappa_2 :: t
  , f :: t -> t
  , sigma_a, sigma_b :: Ordering
  , n_0 :: Integer
  }
\end{code}
\subsection{State}
The algorithm's state consists of the left and right interval endpoints,
|a| and |b|, the function's value at those endpoints, |f_a| and |f_b|,
the interval midpoint, |x_half|, a stepsize limit |delta|, a truncated
probe point value |x_t|, a sign showing where the secant probe point
falls relative to the midpoint |sigma|, and a step count |k|.
\begin{code}
data ITP t = ITP
  { a, b, f_a, f_b, x_t, x_half, delta :: t
  , sigma :: Ordering
  , k :: Integer
  } deriving (Eq, Read, Show)
\end{code}

%if False
\begin{code}
#if DEBUG
type ITPLog t = [ITP t]
logITP :: Monad m => RWST (ITPEnv t) (ITPLog t) (ITP t) m ()
logITP = get >>= tell . (:[])
#else
type ITPLog t = ()
logITP :: Monad m => RWST (ITPEnv t) (ITPLog t) (ITP t) m ()
logITP = pure ()
#endif
{-# ANN itp ("HLint: ignore Redundant multi-way if" :: String) #-}
\end{code}
%endif

\section{The |itp| Function}
Here, it's notable that |n_half| comes from
\autocite[Thm.~2.1]{oliv:taka:itp} which notes worst case bounds of
\begin{equation}
\left\vert\tilde{x}_k-\frac{a_k+b_k}{2}\right\vert
  \leq \varepsilon\cdot 2^{n_\frac{1}{2}-k} - \frac{b_k-a_k}{2}
  \label{bounds:eqn}
\end{equation}
where the midpoint of $[a_k, b_k]$ is represented as a somewhat ambiguous
$x_\frac{1}{2}$. The right-hand side is also used as |r| below. The basic
meaning of \eqref{bounds:eqn} is that how much wider the worst-case
interval width would have been than the actual $k$-th interval's width
bounds how far the $k$-th probe point is from the midpoint of the $k$-th
interval.

\begin{code}
itp :: forall m t . (Monad m, Ord t, RealFloat t, Show t)
  => RWST (ITPEnv t) (ITPLog t) (ITP t) m ()
itp = do
  ITPEnv { epsilon, n_0 } <- ask
  ITP { a, b } <- get
  modify {-" \enspace "-} \s -> s { k = 0 }
  let n_half :: Integer = ceiling (logBase 2 (frac (b - a) (2 * epsilon)))
      n_max  :: Integer = n_half + n_0
      loop :: RWST (ITPEnv t) (ITPLog t) (ITP t) m Bool
      loop = do
\end{code}
        % Calculating parameters
\subsection{Interpolation}
Here, |x_f| is just the ordinary secant method and |x_half| is just the
midpoint of the current interval. The interpolation step seems to refer
to no more than doing a secant method step.
\begin{code}
        logITP
        ITP { a, b, f_a, f_b } <- get
        let x_f = frac (f_b * a - f_a * b) (f_b - f_a)
        modify {-" \enspace "-} \s -> s { x_half = frac (a + b) 2 }
\end{code}
\subsection{Truncation}
Here, |sigma| represents the side of the midpoint the secant method point
|x_f| falls on. The side of the midpoint the secant point falls on is
largely what it gets used to determine, stored as |sigma|. From there,
|delta| is the offset from the midpoint used, whose parameters represent
the superlinearity to be enforced as per \autocite[Thm.~2.3]{oliv:taka:itp}
\begin{equation}
\Delta_{n+1} \sim \kappa_3\Delta_n^{\sqrt{\kappa_2}}
\end{equation}
where $\kappa_3 = \kappa_1^\frac{1}{1+\sqrt{\kappa_2}}$ if $\kappa_2 > 1$
and $\kappa_3 = \frac{1}{2}$ otherwise, though
$1\leq\kappa_2<\phi+1=\phi^2$ suggests the latter is only when
$\kappa_2 = 1$. More directly referring to $\mu=\kappa_3$ as the rate and
$q=\sqrt{\kappa_2}$ as the order of convergence would seem to have been
better choices for parameters, which would give rise to
\begin{eqnarray}
\kappa_1 & = & \mu^{q+1} \\
\kappa_2 & = & q^2
\end{eqnarray}
which would seem to be slightly easier to interpret in terms of error
predictions, perhaps at the cost of one up-front computation to
preprocess them into |kappa_1| and |kappa_2|.
\\
The name for this step seems to be difficult to directly correlate with
the code, because it seems to be using the secant method probe point for
little more than determining which direction to go a distance of |delta|
from the midpoint, otherwise using the midpoint if the secant method
probe point is closer than |delta| to the midpoint.
\begin{code}
        ITPEnv { kappa_1, kappa_2 } <- ask
        modify {-" \enspace "-} \s -> s { delta = kappa_1 * fpowPar (b - a) kappa_2 }
        ITP { x_half } <- get
        modify {-" \enspace "-} \s -> s { sigma = (x_half - x_f) `compare` 0 }
        ITP { delta, sigma } <- get
        if  | delta <= abs (x_half - x_f)
            -> modify {-" \enspace "-} \s -> s { x_t = x_f + sgn sigma * delta }
            | otherwise
            -> modify {-" \enspace "-} \s -> s { x_t = x_half }
\end{code}
\subsection{Projection}
Here use is made of |r| defined according to \eqref{bounds:eqn}.
\begin{code}
        ITPEnv { f } <- ask
        ITP { k, sigma, x_t } <- get
        let r = epsilon * fromInteger (pow 2 (n_max - k)) - frac (b - a) 2
        let x_ITP | abs (x_t - x_half) <= r
                  = x_t
                  | otherwise
                  = x_half - sgn sigma * r
            f_ITP = f x_ITP
\end{code}
\subsection{Updating Interval}
\begin{code}
        ITPEnv { sigma_a, sigma_b } <- ask
        case f_ITP `compare` 0 of
          EQ -> modify {-" \enspace "-} \s -> s { a = x_ITP, f_a = f_ITP
                               , b = x_ITP, f_b = f_ITP }
          o  | o == sigma_a
             -> modify {-" \enspace "-} \s -> s { a = x_ITP, f_a = f_ITP }
             | o == sigma_b
             -> modify {-" \enspace "-} \s -> s { b = x_ITP, f_b = f_ITP }
          _ -> error "error"
        modify {-" \enspace "-} \s -> s { k = k + 1 }
        ITP { a, b, k } <- get
        pure $ (b - a) > 2 * epsilon && k < n_max
  while loop
\end{code}
\section{Conclusion}
The algorithm seems to fail to distinguish a $\delta$ such that
$\left\vert\tilde{x}-x^*\right\vert < \delta$ from a residual bound
$\varepsilon$ such that
$\left\vert f\left(\tilde{x}\right)\right\vert < \varepsilon$. In fact,
no explicit consideration of the magnitude of the residual occurs.
\\
The more conventional notions of the rate $\mu$ and order $q$ of
convergence would be more helpful to use as parameters, as noted in the
introduction.

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
\printbibliography
\end{document}
