\documentclass{article}

%include custom.fmt

%\usepackage{mathpazo}
%\usepackage{utopia}
%\usepackage{lmodern}
\usepackage[dvipsnames]{xcolor}
\usepackage{xspace}
\usepackage{enumitem}
\usepackage{hyperref}
\hypersetup{pdfborder={0 0 0}}

\newcommand{\keyword}[1]{\textsf{\textbf{#1}}}
\newcommand{\id}[1]{\textsf{\textsl{#1}}}
\newcommand{\todo}[1]{\textcolor{red}{TODO: #1}\PackageWarning{TODO:}{#1!}}
\newcommand{\eg}{e.g.\@@\xspace}

% Introducing lifting criteria with a running resumable counter
\newcounter{critCounter}
\newenvironment{introducecrit}{\begin{enumerate}[label=\textbf{(C\arabic*)},ref=(C\arabic*)]\setcounter{enumi}{\value{critCounter}}}{\setcounter{critCounter}{\value{enumi}}\end{enumerate}}

\begin{document}

\title{Lucrative Late Lambda Lifting}

\author{Sebastian Graf}
% \affiliation{%
%   \institution{Karlsruhe Institute of Technology}
%   \streetaddress{Am Fasanengarten 5}
%   \city{Karlsruhe}
%   \postcode{76131}
%   \country{Germany}}
% \email{sebastian.graf@@kit.edu}

\maketitle

\section{Introduction}

\section{Transformation}

\section{When to lift} % Or: Analysis?

Lambda lifting a binding to top-level is always \todo{except when we would replace a parameter occurrence by an application} a sound transformation.
The challenge is in identifying \emph{when} it is beneficial to do so.
This section will discuss operational consequences of lambda lifting, introducing multiple criteria based on a cost model for estimating impact on heap allocations.

\subsection{Syntactic consequences}

Deciding to lift a binding |let f = [x y z] \a b c -> e_1 in e_2| to top-level has the following consequences:

\begin{enumerate}[label=\textbf{(S\arabic*)},ref=(S\arabic*)]
  \item \label{s1} It eliminates the |let| binding.
  \item \label{s2} It creates a new top-level definition.
  \item \label{s3} It replaces all occurrences of |f| in |e_2| by an application of the lifted top-level binding to its former free variables, replacing the whole |let| binding by the term |[f =-> f_up x y z]e_2|. \todo{Maybe less detail here}
  \item \label{s4} All non-top-level variables that occurred in the |let| binding's right-hand side become parameter occurrences.
\end{enumerate}

Consider what happens if |f| occurred in |e_2| as an argument in an application, as in |g 5 x f|. \ref{s3} demands that the argument occurrence of |f| is replaced by an application expression.
This, however, would yield a syntactically invalid expression, because the STG language only allows trivial arguments in an application.

An easy fix would be to bind the complex expression to an auxiliary |let| binding, thereby re-introducing the very allocation we wanted to eliminate through lambda lifting\todo{Move this further down?}. Therefore, we can identify a first criterion for non-beneficial lambda lifts:

\begin{introducecrit}
  \item Don't lift binders that occur as arguments
\end{introducecrit}

\subsection{Operational consequences}

We now ascribe operational symptoms to combinations of syntactic effects. These symptoms justify the derivation of heuristics which will decide when \emph{not} to lift.

\paragraph{Closure growth.} \ref{s1} means we don't allocate a closure on the heap for the |let| binding. On the other hand, \ref{s3} might increase or decrease heap allocation. Consider this example:

\begin{code}
let f = [x y] \a b -> ...
    g = [f x] \d -> f d d + x
in g 5
\end{code}

Should |f| be lifted? It's hard to say without actually seeing the lifted version:

\begin{code}
f_up = \x y a b -> ...;
let g = [x y] \d -> f_up x y d d + x
in g 5
\end{code}

Just counting the number of variables occurring in closures, the effect of \ref{s1} saved us two slots. At the same time, \ref{s3} removes |f| from |g|'s closure (no need to close over the top-level |f_up|), while simultaneously  enlarging it with |f|'s former free variable |y|. The new occurrence of |x| doesn't contribute to closure growth, because it already occurred in |g| prior to lifting. The net result is a reduction of two slots, so  lifting |f| seems worthwhile. In general:

\begin{introducecrit}
  \item \label{h:alloc} Don't lift a binding when doing so would increase closure allocation
\end{introducecrit}

Estimation of closure growth is crucial to identifying beneficial lifting opportunities. We discuss this further in \ref{ssec:cg}.

\paragraph{Calling Convention.} \ref{s4} means that more arguments have to be passed. Depending on the target architecture, this means more stack accesses and/or higher register pressure. Thus

\begin{introducecrit}
  \item Don't lift a binding when the arity of the resulting top-level definition exceeds the number of available hardware registers (\eg 5 arguments on x86\_64)
\end{introducecrit}

\paragraph{Turning known calls into unknown calls.} There's another aspect related to \ref{s4}, relevant in programs with higher-order functions:

\begin{code}
let f = [] \x -> 2*x
    mapF = [f] \xs -> ... f x ...
in mapF [1, 2, 3]
\end{code}

Here, there is a \emph{known call} to |f| in |mapF| that can be lowered as a direct jump to a static address \cite{fastcurry}.  Lifting |mapF| (but not |f|) yields the following program:

\begin{code}
mapF_up = \f xs -> ... f x ...;
let f = [] \x -> 2*x
in mapF_up f [1, 2, 3]
\end{code}


\begin{introducecrit}
  \item Don't lift a binding when doing so would turn known calls into unknown calls
\end{introducecrit}

% These kind of slow calls can never actually occur, because we lift only known functions.
%
% \paragraph{Slow call patterns.} \todo{Align this with the previous paragraph} GHC employs the eval/apply model \cite{fastcurry} for translating function calls. Unknown function calls are lowered as calls to generic apply functions, which are specialised for specific argument patterns, \eg varying on the number of accepted arguments. If there is no matching generic apply function for the given argument pattern, the call is split up into a succession of multiple generic apply calls, allocating partial applications for each but the last generic apply call. Thus, we want to avoid turning slow calls into such \emph{very slow} calls.
% 
% \begin{introducecrit}
%   \item Don't lift a binding when doing so would turn a slow unknown call into a very slow unknown call \todo{call these fast and slow unknown calls instead? Easily confused with fast and slow entrypoints, which are related, but different}
% \end{introducecrit}

\paragraph{Undersaturated calls.} When GHC spots an undersaturated call, it arranges allocation of a partial application that closes over the supplied arguments. Pay attention to the call to |f| in the following example:

\begin{code}
let f = [x] \y z -> x + y + z;
in map (f x) [1, 2, 3]
\end{code}

Here, the undersaturated (\eg curried) call to |f| leads to the allocation of a partial application, carrying two pointers, to |f| and |x|, respectively. What happens when |f| is lambda lifted?

\begin{code}
f_up = \x y z -> x + y + z;
map (f_up x x) [1, 2, 3]
\end{code}

The call to |f_up| will still allocate a partial application, with the only difference that it now also closes over |f|'s free variable |x|, canceling out the beneficial effects of \ref{s1}. Hence

\begin{introducecrit}
  \item Don't lift a binding that has undersaturated calls
\end{introducecrit}

\paragraph{Sharing.} Let's finish with a no-brainer: Lambda lifting updatable bindings (\eg thunks) or constructor bindings is a bad idea, because it destroys sharing, thus possibly duplicating work in each call to the lifted binding.

\begin{introducecrit}
  \item Don't lift a binding that is updatable or a constructor application
\end{introducecrit}

\subsection{Estimating Closure Growth}
\label{ssec:cg}

Of the criterions above, \ref{h:alloc} is the most important for reliable performance gains. It's also the most sophisticated, because it entails estimating closure growth.

Let's revisit the example from above:

\begin{code}
let f = [x y] \a b -> ...
    g = [f x] \d -> f d d + x
in g 5
\end{code}

Will lifting 

\end{document}
