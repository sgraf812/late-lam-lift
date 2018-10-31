\documentclass[draft]{article}

%include custom.fmt

%\usepackage{mathpazo}
%\usepackage{utopia}
%\usepackage{lmodern}
\usepackage{amsmath}
\usepackage{booktabs}
\usepackage{mathpartir}
\usepackage{mathtools}
\usepackage[dvipsnames]{xcolor}
\usepackage{xspace}
\usepackage{todonotes}
\usepackage{enumitem}
\usepackage{hyperref}
\usepackage{cleveref}
\usepackage{csquotes}
\hypersetup{pdfborder={0 0 0}}
\usepackage[backend=bibtex8]{biblatex}

\bibliography{references.bib}

\newcommand{\cf}{cf.\@@\xspace}
\newcommand{\eg}{e.g.,\@@\xspace}
\newcommand{\ie}{i.e.\@@\xspace}

% Tables
\newcommand{\progname}[1]{\texttt{#1}}
\newcommand{\totalname}[1]{#1}
\newcommand{\andmore}[1]{\emph{... and #1 more}}

% Syntax
\newcommand{\keyword}[1]{\textsf{\textbf{#1}}}
\newcommand{\id}[1]{\textsf{\textsl{#1}}\xspace}
\newcommand{\idx}{\id{x}}
\newcommand{\idy}{\id{y}}
\newcommand{\idz}{\id{z}}
\newcommand{\idbs}{\id{bs}}
\newcommand{\idlbs}{\id{lbs}}
\newcommand{\ide}{\id{e}}
\newcommand{\idf}{\id{f}}
\newcommand{\idm}{\id{m}}
\newcommand{\idr}{\id{r}}
\newcommand{\closure}[1]{[\mskip1.5mu #1 \mskip1.5mu]}
\newcommand{\mkRhs}[2]{\lambda #1 \to #2}
\newcommand{\mkBind}[3]{#1 \mathrel{=} \closure{#2} #3}
\newcommand{\mkBindr}[3]{\overline{\mkBind{#1}{#2}{#3}}}
\newcommand{\mkLetb}[2]{\keyword{let}\; #1\; \keyword{in}\; #2}
\newcommand{\mkLet}[5]{\mkLetb{\mkBind{#1}{#2}{\mkRhs{#3}{#4}}}{#5}}
\newcommand{\mkLetr}[5]{\mkLetb{\mkBindr{#1}{#2}{\mkRhs{#3}{#4}}}{#5}}
\newcommand{\sfop}[1]{\textsf{#1}\xspace}
\newcommand{\fun}[1]{\textsf{#1}\xspace}
\newcommand{\ty}[1]{\textsf{#1}\xspace}
\newcommand{\idiom}[1]{\left\llbracket#1\right\rrbracket}
\newcommand{\writer}[2]{\mathcal{W}_#1\,#2}
\newcommand{\eff}[1]{\left\langle#1\right\rangle}
\newcommand{\lift}{\fun{lift}}
\newcommand{\liftv}{\fun{lift-var}}
\newcommand{\liftb}{\fun{lift-bind}}
\newcommand{\abs}{\fun{abstract}}
\newcommand{\expand}{\fun{expand-closures}}
\newcommand{\decide}{\fun{decide-lift}}
\newcommand{\recurse}{\fun{recurse}}
\newcommand{\note}{\fun{note}}
\newcommand{\fvs}{\fun{fvs}}
\newcommand{\expander}{\ty{Expander}}
\newcommand{\var}{\ty{Var}}
\newcommand{\expr}{\ty{Expr}}
\newcommand{\bindgr}{\ty{Bind}}
\newcommand{\emptybind}{\varepsilon}
\newcommand{\wrap}{\fun{wrap}}
\newcommand{\dom}[1]{\sfop{dom}\,#1}
\newcommand{\absids}{\alpha}
\newcommand{\added}{\varphi^+}
\newcommand{\removed}{\varphi^-}
\newcommand{\cg}{\fun{cl-gr}}
\newcommand{\cgb}{\fun{cl-gr-bind}}
\newcommand{\cgr}{\fun{cl-gr-rhs}}
\newcommand{\growth}{\fun{growth}}
\newcommand{\local}{\fun{local}}
\newcommand{\zinf}{\mathbb{Z}_{\infty}}
\newcommand{\card}[1]{\left\vert#1\right\vert}

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
\label{sec:trans}

Lambda lifting is a long- and well-known transformation
\parencite{Johnsson1985}, traditionally used for compiling functional programs
to supercombinators.  Our use case for lambda lifting is unique in that it
operates on terms of the \emph{spineless tagless G-machine} (STG)
\parencite{stg} as currently implemented \parencite{fastcurry} in GHC and in
that we only lift \emph{selectively}.  The extension of Johnsson's formulation
to STG terms is straight-forward, but it's still worth showing how the
transformation integrates the decision logic for which bindings are going to be
lambda lifted.

Central to the transformation is the construction of the set of \emph{required
variables} \textcite{Johnsson1985} for a binding.  Because we operate late in
the pipeline of GHC, we can assume that every recursive binding group
corresponds to a strongly-connected component of the dependency graph.  This
means that construction of the required set simplifies to joining the free
variable sets of the binding group, once, for the whole binding group.

\subsection{Syntax}

Although STG is but a tiny language compared to typical surface languages such as Haskell, its definition \parencite{fastcurry} still contains much detail irrelevant to lambda lifting.
As can be seen in \cref{fig:syntax}, we therefore adopt a simple lambda calculus with |let| bindings as in \textcite{Johnsson1985}, with a few STG-inspired features:

\begin{enumerate}
\item |let| bindings are annotated with the non-top-level free variables of the right-hand side (RHS) they bind
\item Every lambda abstraction is the right-hand side of a |let| binding
\item Arguments and heads in an application expression are all atomic (\eg variable references)
\end{enumerate}

We decomposed |let| expressions into smaller syntactic forms for the simple
reason that it allows the analysis and transformation to be defined in more
granular (and thus more easily understood) steps.

\begin{figure}[h]
\begin{alignat*}{4}
\text{Variables} &\quad& f,x,y &&&&\quad& \\
\text{Expressions} && e & {}\Coloneqq{} && x && \text{Variable} \\
            &&   & \mathwithin{{}\Coloneqq{}}{\mid} && f\; x_1\ldots\,x_n && \text{Function call} \\
            &&   & \mathwithin{{}\Coloneqq{}}{\mid} && \mkLetb{b}{e} && \text{Recursive \keyword{let}} \\
\text{Bindings} && b & {}\Coloneqq{} && \overline{f_i \mathrel{=} [\mskip1.5mu x_{i,1} \ldots\, x_{i,n_i}\mskip1.5mu] \mskip1.5mu r_i} && \\
\text{Right-hand sides} && r & {}\Coloneqq{} && \lambda \mskip1.5mu y_1 \ldots\,y_m\to e && \\
\end{alignat*}
\caption{An STG-like untyped lambda calculus}
\label{fig:syntax}
\end{figure}

\subsection{Algorithm}

Our implementation extends the original formulation of \textcite{Johnsson1985} to STG terms, by exploiting and maintaining closure annotations.
We will recap our variant of the algorithm in its whole here.
It is assumed that all variables have unique names and that there is a sufficient supply of fresh names from which to draw.

We'll define a side-effecting function, \lift, recursively over the term structure. This is its signature:

\todo[inline]{Take inspiration in "Implementing functional languages: a tutorial" and collect super-combinators afterwards for better separation of concerns. Is that possible? After all, that would influence the lifting decision!}

\[
\lift_{\mathunderscore}(\mathunderscore) \colon \expander \to \expr \to \writer{\bindgr}{\expr}
\]
\todo{I think the occurrences of body expression etc. need to be meta-variables.}

As its first argument, \lift takes an \expander, which is a partial function from lifted binders to their sets of required variables.
These are the additional variables we have to pass at call sites after lifting.
The expander is extended every time we decide to lambda lift a binding.
It plays a similar role as the $E_f$ set in \textcite{Johnsson1985}.
We write $\dom{\absids}$ for the domain of the expander $\absids$ and $\absids[\idx \mapsto S]$ to denote extension of the expander function, so that the result maps $\idx$ to $S$ and all other identifiers by delegating to $\absids$.

The second argument is the expression that is to be lambda lifted.
A call to \lift results in an expression that no longer contains any bindings that were lifted.
The lifted bindings are emitted as a side-effect of the \emph{writer monad}, denoted by $\writer{\bindgr}{\mathunderscore}$.

\subsubsection{Side-effects}

\todo{Properly define the structure? Or is this 'obvious'?}
The following syntax, inspired by \emph{idiom brackets} \parencite{applicative} and \emph{bang notation}\footnote{http://docs.idris-lang.org/en/v1.3.0/tutorial/interfaces.html}, will allow concise notation while hiding sprawling state threading:

\[
  \idiom{E[\eff{e_1}, ..., \eff{e_n}]}
\]

This denotes a side-effecting computation that, when executed, will perform the side-effecting subcomputations $e_i$ in order (any fixed order will do for us).
After that, it will lift the otherwise pure context $E$ over the results of the subcomputations.

In addition, we make use of the monadic bind operators $>\!\!>\!\!=$ and $>\!\!>$, defined in the usual way.
The primitive operation $\note$ takes as argument a binding group and merges its bindings into the contextual binding group tracked by the writer monad.

\subsubsection{Variables}

Let's begin with the variable case.

\begin{alignat*}{2}
&\lift_\absids(\idx) &{}={}&
  \begin{cases}
    \idiom{\idx},                        & \idx \notin \dom{\absids} \\
    \idiom{\idx\; \idy_1 \ldots \idy_n}, & \absids(\idx) = \{ \idy_1, \ldots, \idy_n \}
  \end{cases} \\
\end{alignat*}


We check if the variable was lifted to top-level by looking it up in the supplied expander mapping $\absids$ and if so, we apply it to its newly required variables.
There are no bindings occuring that could be lambda lifted, hence the function performs no actual side-effects.

\subsubsection{Applications}

\label{sssec:app}

Handling function application correctly is a little subtle, because only variables are allowed in argument position.
When such an argument variable's binding is lifted to top-level, it turns into a non-atomic application expression, violating the STG invariants.
Each such application must be bound to an enclosing |let| binding
\footnote{To keep the specification reasonably simple, we also do so for non-lifted identifiers and assume that the compiler can do the trivial rewrite $\mkLet{\idy}{\idx}{}{\idx}{E[\idy]} \Longrightarrow E[\idx]$ for us.}:

\todo{The application rule is unnecessarily complicated because we support occurrences of lifted binders in argument position. Lifting such binders isn't worthwhile anyway (see \cref{sec:analysis}). Maybe just say that we don't allow it?}

\[
\lift_\absids(\idf\; \idx_1 \ldots \idx_n) = \idiom{(\wrap_\absids(\idx_n) \circ \ldots \circ \wrap_\absids(\idx_1))(\eff{\lift_\absids(\idf)}\; \idx_1' \ldots \idx_n')} \\ \]

The notation $\idx'$ chooses a fresh name for $\idx$ in a consistent fashion.
The application head \idf is handled by an effectful recursive call to \lift.
Syntactically heavy |let| wrapping is outsourced into a helper function \wrap:

\[
\wrap_\absids(\idx)(\ide) =
  \begin{cases}
    \mkLet{\idx'}{\idx}{}{\idx}{\ide}, & \idx \notin \dom{\absids} \\
    \mkLet{\idx'}{}{\idy_1 \ldots \idy_n}{\idx\; \idy_1 \ldots \idy_n}{\ide}, & \absids(\idx) = \{ \idy_1, \ldots, \idy_n \} \\
  \end{cases} \\
\]

\subsubsection{Let Bindings}

Hardly surprising, the meat of the transformation hides in the handling of |let| bindings.
This can be broken down into three separate functions:
\[
\lift_\absids(\mkLetb{\idbs}{\ide}) = (\recurse(\ide) \circ \decide_\absids \circ \expand_\absids)(\idbs)
\]

\begin{enumerate}
\item The first step is to expand closures mentioned in $\idbs$ with the help of $\absids$.
\item Second, a heuristic (that of \cref{sec:analysis}, for example) decides whether to lift the binding group $\idbs$ to top-level or not.
\item Depending on that decision, the binding group is \note{}d to be lifted to top-level and syntactic subentities of the |let| binding are traversed with the updated expander.
\end{enumerate}

\begin{alignat*}{2}
\expand_\absids(\mkBindr{\idf_i}{\idx_1 \ldots \idx_{n_i}}{\idr_i}) &&{}={}& \mkBindr{\idf_i}{\idy_1 \ldots \idy_{n'_i}}{\idr_i} \\
\text{where}\qquad\qquad &&& \\
\{\idy_1\ldots \idy_{n'_i}\} &&{}={}& \bigcup_{j=1}^{n_i}
  \begin{cases}
    \idx_j, & \idx_j \notin \dom{\absids} \\
    \absids(\idx_j), & \text{otherwise}
  \end{cases}
\end{alignat*}

\todo{Not happy with the indices. $\idy_{i,1}$ maybe? Applies to many more examples.}

\expand substitutes all occurences of lifted binders (those that are in $\dom{\absids}$) in closures of a given binding group by their required set.

\begin{alignat*}{2}
\decide_\absids(\idbs) &&{}={}&
  \begin{cases}
    (\emptybind,\absids',\abs_{\absids'}(\idbs)), & \text{if \idbs should be lifted} \\
    (\idbs, \absids, \emptybind), & \text{otherwise} \\
  \end{cases} \\
\text{where}\qquad &&& \\
\absids' &&{}={}& \absids\left[\overline{\idf_i \mapsto \fvs(\idbs)}\right] \text{for } \mkBindr{\idf_i}{\mathunderscore}{\mathunderscore} = \idbs
\end{alignat*}

\decide returns a triple of a binding group that remains with the local |let| binding, an updated expander and a binding group prepared to be lifted to top-level.
Depending on whether the argument $\idbs$ is decided to be lifted or not, either the returned local binding group or the $\abs$ed binding group is empty.
In case the binding is to be lifted, the expander is updated to map the newly lifted bindings to their required set.
\[
\fvs(\mkBindr{\idf_i}{\idx_1 \ldots \idx_{n_i}}{\mathunderscore}) = \bigcup_i \{\idx_1, \ldots, \idx_{n_i} \} \setminus \overline{\idf_i}
\]

The required set consists of the free variables of each binding's RHS, conveniently available in syntax, minus the defined binders themselves.
Note that the required set of each binder of the same binding group will be identical (\cf begin of \cref{sec:trans}).
\[
\abs_\absids(\mkBindr{\idf_i}{\idx_1 \ldots \idx_{n_i}}{\mkRhs{\idy_1 \ldots \idy_{m_i}}{\ide_i}}) = \mkBindr{\idf_i}{}{\mkRhs{\absids(\idf_i)\; \idy_1 \ldots \idy_{m_i}}{\ide_i}}
\]

The abstraction step is performed in \abs, where closure variables are removed in favor of additional parameters, one for each element of the respective binding's required set.
\[
\recurse(\ide)(\idbs, \absids, \idlbs) = \liftb_\absids(\idlbs) >\!\!>\!\!= \note >\!\!> \idiom{\mkLetb{\eff{\liftb_\absids(\idbs)}}{\eff{\lift_\absids(\ide)}}}
\]

In the final step of the |let| \enquote{pipeline}, the algorithm recurses into every subexpression of the |let| binding.
The binding group to be lifted is transformed first, after which it is added to the contextual top-level binding group of the writer monad.
Finally, the binding group that remains locally bound is traversed, as well as the original |let| body.
The result is again wrapped up in a |let| and returned\footnote{Similar to the application case, we assume that the compiler performs the obvious rewrite $\mkLetb{\emptybind}{e} \Longrightarrow e$.}.

What remains is the trivial, but noisy definition of the \liftb traversal:

\[
\liftb_\absids(\mkBindr{\idf_i}{\idx_1 \ldots \idx_{n_i}}{\mkRhs{\idy_1 \ldots \idy_{m_i}}{\ide_i}}) = \idiom{\mkBindr{\idf_i}{\idx_1 \ldots \idx_{n_i}}{\mkRhs{\idy_1 \ldots \idy_{m_i}}{\eff{\lift_\absids(\ide_i)}}}} \\
\]

\section{When to lift} % Or: Analysis?

\label{sec:analysis}

Lambda lifting a binding to top-level is always a sound transformation.  The
challenge is in identifying \emph{when} it is beneficial to do so.  This
section will discuss operational consequences of lambda lifting, introducing
multiple criteria based on a cost model for estimating impact on heap
allocations.

We'll take a somewhat loose approach to following the STG invariants in our
examples (regarding giving all complex subexpressions a name, in particular),
but will point out the details if need be.

\subsection{Syntactic consequences}

Deciding to lift a binding |let f = [x y z] \a b c -> e_1 in e_2| to top-level
has the following consequences:

\begin{enumerate}[label=\textbf{(S\arabic*)},ref=(S\arabic*)]
  \item \label{s1} It eliminates the |let| binding.
  \item \label{s2} It creates a new top-level definition.
  \item \label{s3} It replaces all occurrences of |f| in |e_2| by an
    application of the lifted top-level binding to its former free variables,
    replacing the whole |let| binding by the term |[f =-> f_up x y z]e_2|.\footnote{Actually, this will also need to give a name to new non-atomic argument expressions (\cf \cref{sssec:app}). We'll argue shortly that there is hardly any benefit in allowing these cases.}
  \item \label{s4} All non-top-level variables that occurred in the |let| binding's right-hand side become parameter occurrences.
\end{enumerate}

Naming seemingly obvious things this way means we can precisely talk about
\emph{why} we are suffering from one of the operational symptoms discussed
next.

\subsection{Operational consequences}

We now ascribe operational symptoms to combinations of syntactic effects. These
symptoms justify the derivation of heuristics which will decide when \emph{not}
to lift.

\paragraph{Argument occurrences.} Consider what happens if |f| occurred in the
|let| body |e_2| as an argument in an application, as in |g 5 x f|.  \ref{s3}
demands that the argument occurrence of |f| is replaced by an application
expression.  This, however, would yield a syntactically invalid expression
because the STG language only allows trivial arguments in an application.

The transformation from \cref{sec:trans} will immediately wrap the application
in a |let| binding for the complex argument expression: |g 5 x f ==> let f' =
f_up x y z in g 5 x f'|.  But this just reintroduces at every call site the very
allocation we wanted to eliminate through lambda lifting! Therefore, we can identify a
first criterion for non-beneficial lambda lifts:

\begin{introducecrit}
  \item Don't lift binders that occur as arguments
\end{introducecrit}

A welcome side-effect is that the application case of the transformation in
\cref{sssec:app} becomes much simpler: The complicated \wrap business becomes
unnecessary.

\paragraph{Closure growth.} \ref{s1} means we don't allocate a closure on the
heap for the |let| binding. On the other hand, \ref{s3} might increase or
decrease heap allocation, which can be captured by a metric we call
\emph{closure growth}. Consider this example:

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

Just counting the number of variables occurring in closures, the effect of
\ref{s1} saved us two slots. At the same time, \ref{s3} removes |f| from |g|'s
closure (no need to close over the top-level |f_up|), while simultaneously
enlarging it with |f|'s former free variable |y|. The new occurrence of |x|
doesn't contribute to closure growth, because it already occurred in |g| prior
to lifting. The net result is a reduction of two slots, so lifting |f| seems
worthwhile. In general:

\begin{introducecrit}
  \item \label{h:alloc} Don't lift a binding when doing so would increase closure allocation
\end{introducecrit}

Note that this also includes handling of |let| bindings for partial
applications that are allocated when GHC spots an undersaturated call.

Estimation of closure growth is crucial to identifying beneficial lifting
opportunities. We discuss this further in \cref{ssec:cg}.

\paragraph{Calling Convention.} \ref{s4} means that more arguments have to be passed. Depending on the target architecture, this entails more stack accesses and/or higher register pressure. Thus

\begin{introducecrit}
  \item Don't lift a binding when the arity of the resulting top-level definition exceeds the number of available argument registers of the employed calling convention (\eg 5 arguments for GHC on x86\_64)
\end{introducecrit}

One could argue that we can still lift a function when its arity won't change.
But in that case, the function would not have any free variables to begin with
and could just be floated to top-level. As is the case with GHC's full laziness
transformation, we assume that this already happened in a prior pass.

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

\paragraph{Code size.} \ref{s2} (and, to a lesser extent, all other consequences) have the potential to increase or decrease code size. We regard this a secondary concern, but will have a look at it in \cref{sec:eval}.

\paragraph{Sharing.} Let's finish with a no-brainer: Lambda lifting updatable bindings (\eg thunks) or constructor bindings is a bad idea, because it destroys sharing, thus possibly duplicating work in each call to the lifted binding.

\begin{introducecrit}
  \item Don't lift a binding that is updatable or a constructor application
\end{introducecrit}

\subsection{Estimating Closure Growth}
\label{ssec:cg}

Of the criterions above, \ref{h:alloc} is the most important for reliable performance gains.
It's also the most sophisticated, because it entails estimating closure growth.

\subsubsection{Motivation}

Let's revisit the example from above:

\begin{code}
let f = [x y] \a b -> ...
    g = [f x] \d -> f d d + x
in g 5
\end{code}

We concluded that lifting |f| would be beneficial, saving us allocation of two free variable slots.
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
Hence there is no actual closure growth happening under the multi-shot binding |g| and |f| is good to lift.

The solution is to denote closure growth in the (not quite max-plus) algebra $\zinf = \mathbb{Z} \cup \{\infty\}$ and denote positive closure growth under a multi-shot lambda by $\infty$.

\subsubsection{Design}

Applied to our simple STG language, we can define a function $\cg$ (short for closure growth) with the following signature:
\todo{Maybe add the syntactic sort we operate on as a superscript?}

\[
\cg_{\mathunderscore\,\mathunderscore}(\mathunderscore) \colon \mathcal{P}(\var) \to \mathcal{P}(\var) \to \expr \to \zinf
\]

Given two sets of variables for added and removed closure variables,
respectively, it maps expressions to the closure growth resulting from 
\begin{itemize}
\item adding variables from the first set everywhere a variable from the second
      set is referenced 
\item and removing all closure variables mentioned in the second set.
\end{itemize}

In the lifting algorithm from \cref{sec:trans}, \cg would be consulted as part
of the lifting decision to estimate the total effect on allocations.  Assuming
we were to decide whether to lift the binding group $\overline{\idf_i}$ out of
an expression $\mkLetr{\idf_i}{\idx_1 \ldots \idx_{n_i}}{\idy_1 \ldots
\idy_{m_i}}{\ide_i}{\ide}$, the following expression conservatively estimates
the effects on heap allocation for performing the lift:

\[
\cg_{\absids'(\idf_1)\,\{\overline{\idf_i}\}}(\mkLetr{\idf_i}{}{\idx_1 \ldots \idx_{n_i} \idy_1 \ldots \idy_{m_i}}{\ide_i}{\ide}) - \sum_i n_i
\]

With the \emph{required set} $\absids'(\idf_1)$ passed as the first argument and with $\{\overline{\idf_i}\}$ for the second set (\ie the binders for which lifting is to be decided).

Note that we logically lambda-lifted the binding group in question without actually floating out the binding.
The reasons for that are twofold:
Firstly, the reductions in closure allocation resulting from that lift are accounted separately in the trailing sum expression, capturing the effects of \ref{s1}.
Secondly, the lifted binding group isn't affected by closure growth (where there are no free variables, nothing can grow or shrink), which is entirely a symptom of \ref{s3}.

In practice, we require that this metric is non-positive to allow the lambda lift.

\subsubsection{Implementation}

The cases for variables and applications are trivial, because they don't allocate:
\begin{alignat*}{2}
\cg_{\added\removed}(\idx) &&{}={}& 0 \\
\cg_{\added\removed}(\idf\; \idx_1 \ldots \idx_n) &&{}={}& 0
\end{alignat*}
As before, the complexity hides in |let| bindings and its syntactic components.
We'll break them down one layer at a time. This makes the |let| rule itself
nicely compositional, because it delegates most of its logic to $\cgb$:
\[
\cg_{\added\removed}(\mkLetb{\idbs}{\ide}) = \cgb_{\added\removed}(\idbs) + \cg_{\added\removed}(\ide)
\]

Next, we look at how binding groups are measured:

\begin{alignat*}{2}
\cgb_{\added\removed}(\mkBindr{\idf_i}{\idx_1 \ldots \idx_{n_i}}{\idr_i})&&{}={}& \sum_i \growth_i + \sum_i \cgr_{\added\removed}(\idr_i) \\
\growth_i &&{}={}&
  \begin{cases}
    \card{\added \setminus \{\idx_1,\ldots,\idx_{n_i}\}} - \nu_i, & \text{if $\nu_i > 0$} \\
    0, & \text{otherwise} \\
  \end{cases} \\
\nu_i &&{}={}& \card{\{\idx_1,\ldots,\idx_{n_i}\} \cap \removed}
\end{alignat*}

The \growth component accounts for allocating each closure of the binding
group. Whenever a closure mentions one of the variables to be removed (\ie
$\removed$, the bindings to be lifted), we count the number of variables that
are removed in $\nu$ and subtract them from the number of variables in $\added$
(\ie the required set of the binding group to lift) that didn't occur in the
closure before.

The call to $\cgr$ accounts for closure growth of right-hand sides:

\begin{alignat*}{2}
\cgr_{\added\removed}(\mkRhs{\ldots}{\ide_i})&&{}={}& \cgr_{\added\removed}(\idr_i) * [\sigma, \tau] \\
\sigma &&{}={}& 
  \begin{cases}
    1, & \text{\ide is entered at least once} \\
    0, & \text{otherwise} \\
  \end{cases} \\
\tau &&{}={}& 
  \begin{cases}
    0, & \text{\ide is never entered} \\
    1, & \text{\ide is entered at most once} \\
    1, & \text{the RHS is bound to a thunk} \\
    \infty, & \text{otherwise} \\
  \end{cases} \\
n * [\sigma, \tau] &&{}={}&
  \begin{cases}
    n * \sigma, & l < 0 \\
    n * \tau,   & \text{otherwise} \\
  \end{cases} \\
\end{alignat*}

The right-hand sides of a |let| binding might or might not be entered, so we
cannot rely on a beneficial negative closure growth to occur in all cases.
Likewise, without any further analysis information, we can't say if a
right-hand side is entered multiple times. Hence, the uninformed conservative
approximation would be to return $\infty$ whenever there is positive closure
growth in a RHS and 0 otherwise.

That would be disastrous for analysis precision! Fortunately, GHC has access to
cardinality information from its demand analyser \parencite{dmd} \todo{What to cite? Progress
on the new demand analysis paper seemed to have stalled. The cardinality paper?
The old demand analysis paper from 2006? Both?}. Demand analysis estimates lower
and upper bounds ($\sigma$ and $\tau$ above) on how many times a RHS is entered
relative to its defining expression.

Most importantly, this identifies one-shot lambdas ($\tau = 1$), under which
case a positive closure growth doesn't lead to an infinite closure growth for
the whole RHS. But there's also the beneficial case of negative closure growth
under a strictly called lambda ($\sigma = 1$), where we gain precision by not
having to fall back to returning 0.

\vspace{2mm}

One final remark regarding analysis performance: \cg operates directly on STG expressions.
This means the cost function has to traverse whole syntax trees \emph{for every lifting decision}.

We remedy this by first abstracting the syntax tree into a \emph{skeleton}, retaining only the information necessary for our analysis.
In particular, this includes allocated closures and their free variables, but also occurrences of multi-shot lambda abstractions.
Additionally, there are the usual \enquote{glue operators}, such as sequence (\eg the case scrutinee is evaluated whenever one of the case alternatives is), choice (\eg one of the case alternatives is evaluated \emph{mutually exclusively}) and an identity (\ie literals don't allocate).
This also helps to split the complex |let| case into more manageable chunks.

\section{Related Work}

\textcite{Johnsson1985} was the first to conceive lambda lifting as a code generation scheme for functional languages.

\section{Evaluation}
\label{sec:eval}

In order to assess effectiveness of our new optimisation, we measured
performance on the \texttt{nofib} benchmark suite \parencite{nofib} against a
GHC 8.6.1
release\footnote{\url{https://github.com/ghc/ghc/tree/0d2cdec78471728a0f2c487581d36acda68bb941}}.

We will first look at how our chosen parameterisation (\eg the optimisation
with all heuristics activated as advertised) performs in comparison to the
baseline. Subsequently, we will justify the choice by comparing with other
parameterisations that selectively abandon or vary the heuristics of
\cref{sec:analysis}.

\subsection{Effectiveness}

The results of comparing our chosen configuration with the baseline can be seen in \cref{tbl:ll}.

\begin{table}
  \centering
  \begin{tabular}{lrrr}
    \toprule
    Program & \multicolumn{1}{c}{Bytes Allocated} & \multicolumn{1}{c}{Instructions executed} \\
    \midrule
    \input{tables/ll-nofib-table.tex}
    \bottomrule
  \end{tabular}
  \caption{
    Interesting programs with respect to instructions executed, from the same run as \cref{tbl:nofib}.
    Excluded were those runs with improvements of less than 3\% and regressions of less than 1\%.
  }
  \label{tbl:ll}
\end{table}

\listoftodos

\printbibliography

\end{document}
