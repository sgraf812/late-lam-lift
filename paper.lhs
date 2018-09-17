\documentclass{article}

%include custom.fmt

%\usepackage{mathpazo}
%\usepackage{utopia}
%\usepackage{lmodern}
\usepackage{amsmath}
\usepackage{mathtools}
\usepackage[dvipsnames]{xcolor}
\usepackage{xspace}
\usepackage{enumitem}
\usepackage{hyperref}
\usepackage{cleveref}
\usepackage{csquotes}
\hypersetup{pdfborder={0 0 0}}
\usepackage[backend=bibtex8]{biblatex}

\bibliography{references.bib}

\newcommand{\keyword}[1]{\textsf{\textbf{#1}}}
\newcommand{\id}[1]{\textsf{\textsl{#1}}}
\newcommand{\todo}[1]{\textcolor{red}{TODO: #1}\PackageWarning{TODO:}{#1!}}
\newcommand{\eg}{e.g.\@@\xspace}

% https://tex.stackexchange.com/a/268475/52414
\newlength\stextwidth
\newcommand\makesamewidth[3][c]{%
  \settowidth{\stextwidth}{#2}%
    \makebox[\stextwidth][#1]{#3}%
}
\newlength\smathtextwidth
\newcommand\mathmakesamewidth[3][c]{%
  \settowidth{\smathtextwidth}{$#2$}%
    \mathmakebox[\smathtextwidth][#1]{#3}%
}
\newcommand\mathwithin[2]{%
  \mathmakesamewidth[c]{#1}{#2}
}

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

Lambda lifting is a well-known technique \parencite{Johnsson1985}.
Although Johnsson's original algorithm runs in wort-case cubic time relative to the size of the input program, \textcite{optimal-lift} gave an algorithm that runs in $\mathcal{O}(n^2)$.

Our lambda lifting transformation is unique in that it operates on terms of the \emph{spineless tagless G-machine} (STG) \parencite{stg} as currently implemented \parencite{fastcurry} in GHC.
This means we can assume that the nesting structure of bindings corresponds to the condensation (the directed acyclic graph of strongly connected components) of the dependency graph. \todo{less detail? less language?}
Additionally, every binding in a (recursive) |let| expression is annotated with the free variables it closes over.
The combination of both properties allows efficient construction of the set of \emph{required} \todo{any better names? former free variables, abstraction variables...} variables for a total complexity of $\mathcal{O}(n^2)$, as we shall see.

\subsection{Syntax}

Although STG is but a tiny language compared to typical surface languages such as Haskell, its definition \parencite{fastcurry} still contains much detail irrelevant to lambda lifting.
As can be seen in \cref{fig:syntax}, we therefore adopt a simple lambda calculus with |let| bindings as in \textcite{Johnsson1985}, with a few STG-inspired features:

\begin{enumerate}
\item |let| bindings are annotated with the free variables they close over
\item Arguments in an application expression are all atomic (\eg variable references)
\item Every lambda abstraction is the right-hand side of a |let| binding
\item All applications are fully saturated
\end{enumerate}

\begin{figure}[h]
\begin{alignat*}{4}
\text{Variables} &\quad& f,x,y &&&&\quad& \\
\text{Expressions} && e & {}\Coloneqq{} && x && \text{Variable} \\
            &&   & \mathwithin{{}\Coloneqq{}}{\mid} && f\; x_1...\,x_n && \text{Saturated function call} \\
            &&   & \mathwithin{{}\Coloneqq{}}{\mid} && \keyword{let} && \text{Recursive \keyword{let}} \\
            &&   &&& \quad \overline{f_i \mathrel{=} [\mskip1.5mu x_{i,1}, ..., x_{i,n}\mskip1.5mu] \lambda \mskip1.5mu y_{i,1}\;...\;y_{i,m}\to e_i} && \\
            &&   &&& \keyword{in}\;e && \\
\end{alignat*}
\caption{An STG-like untyped lambda calculus}
\label{fig:syntax}
\end{figure}

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

Here, there is a \emph{known call} to |f| in |mapF| that can be lowered as a direct jump to a static address \parencite{fastcurry}.  Lifting |mapF| (but not |f|) yields the following program:

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

We concluded that lifting |f| would be beneficial, saving us allocation of one free variable slot.
There are two effects at play here.
Not having to allocate the closure of |f| due to \ref{s1} always leads to a one-time benefit.
Simultaneously, each closure occurrence of |f| would be replaced by its referenced free variables.
Removing |f| leads to a saving of one slot per closure, but the free variables |x| and |y| each occupy a closure slots in turn.
Of these, only |y| really contributes to closure growth, because |x| already occurred in the single remaining closure of |g|.

This phenomenon is amplified whenever allocation happens under a multi-shot lambda, as the following example demonstrates:

\begin{code}
let f = [x y] \a b -> ...
    g = [f x] \d ->
      let h = [f] \e -> f e e
      in h d
in g 1 + g 2 + g 3
\end{code}

Is it still beneficial to lift |f|?
Following our reasoning, we still save two slots from |f|'s closure, the closure of |g| doesn't grow and the closure |h| grows by one.
We conclude that lifting |f| saves us one closure slot.
But that's nonsense!
Since |g| is called thrice, the closure for |h| also gets allocated three times relative to single allocations for the closures of |f| and |g|.

In general, |h| might be occuring inside a recursive function, for which we can't reliably estimate how many times its closure will be allocated.
Disallowing to lift any binding which is called inside a closure under such a multi-shot lambda is conservative, but rules out worthwhile cases like this:

\begin{code}
let f = [x y] \a b -> ...
    g = [f x y] \d ->
      let h_1 = [f] \e -> f e e
          h_2 = [f x y] \e -> f e e + x + y
      in h_1 d + h_2 d
in g 1 + g 2 + g 3
\end{code}

Here, the closure of |h_1| grows by one, whereas that of |h_2| shrinks by one, cancelling each other out.
We express this in our cost model by an infinite closure growth whenever there was any positive closure growth under a multi-shot lambda.

One final remark regarding analysis performance.
\todo{equation} operates directly on STG expressions.
This means the cost function has to traverse whole syntax trees \emph{for every lifting decision}.

Instead, our implementation first abstracts the syntax tree into a \emph{skeleton}, retaining only the information necessary for our analysis.
In particular, this includes allocated closures and their free variables, but also occurrences of multi-shot lambda abstractions.
Additionally, there are the usual \enquote{glue operators}, such as sequence (\eg the case scrutinee is evaluated whenever one of the case alternatives is), choice (\eg one of the case alternatives is evaluated \emph{mutually exclusively}) and an identity (\eg literals don't allocate).

\printbibliography

\end{document}
