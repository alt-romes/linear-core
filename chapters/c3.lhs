%include polycode.fmt

\chapter{Proposed Work}

% \section{Foreword}

% This document is a work in progress proposal that I will deliver (in an extended
% form) at the end of the semester as part of my master thesis preparation. The
% document still needs a proper introduction, lengthy background and related work
% section  such that an outsider might understand what I propose to do. However,
% this initial iteration is instead targeted at those already familiar with the
% problem and serves as a (less bureaucratic) proposal on linting linearity in
% Core and to showcase the preliminary progress I have made so far.


\section{Motivation}

Since the publication of Linear Haskell~\cite{cite:linearhaskell} and its
implementation in GHC 9.0, Haskell's type system supports linearity annotations
in functions. Linear Haskell effectively brings linear types to a mainstream,
pure, and lazy functional language. Concretely, Haskell function types can be
annotated with a multiplicity, where a multiplicity of \texttt{1} requires the
argument to be consumed exactly once and a multiplicity of \texttt{Many} allows
the function argument to be consumed unrestrictedly, i.e., zero or more times.

% A function is linear if it consumes its arguments exactly once when it itself
% is consumed exactly once.

As mentioned in Section~\ref{sec:core}, GHC Haskell features two typed
languages in its pipeline: Haskell and Core.
%
Core is a much smaller language than the whole of Haskell (even though we can
compile the whole of Haskell to Core).
%
The addition of linear types to
GHC Haskell required changing the type system of both languages. However,
Linear Haskell only describes an extension to the surface-level Haskell type
system, not Core. Nonetheless, in practice, Core is linearity-aware.

We want Core and its type system to give us guarantees about desugaring and
optimizing transformations regard to linearity just as Core does for types -- a
linearly typed Core ensures that linearly-typed programs remain correct both
after desugaring and across all GHC optimizing transformations, i.e.~linearity
is preserved when desugaring and optimisations should not destroy linearity.

% \todo[inline]{Nao e necessario reexplicar o que e o Core, o que e
%   preciso aqui e explicar que o desugaring tem anotacoes de
%   linearidade mas que sao ignoradas e explicar porque. Em particular,
%   algum do texto que esta mais a frente a dizer as variaveis sao
%   anotadas no Core mas que e tudo ignorado deve ficar claro nesta altura}

% This type
% checker (called \emph{Lint}) gives us guarantees of correctness in face of all
% the complex transformations a Haskell program undergoes, such as desugaring and
% core-to-core optimization passes, because the linter is always run on the resulting code
% before ultimately being compiled to (untyped) machine code.

% System FC is the formal system in which the implementation of GHC's intermediate
% representation language \emph{Core} is based on.


In this sense, Core is already annotated with linearity, but its type-checker
\textbf{currently ignores linearity annotations}.
%
In spite of the strong formal foundations of linear types driving the
implementation, their interaction with the whole of GHC is still far from
trivial. The implemented type system cannot accomodate several optimising
transformations that produce programs which violate linearity
\emph{syntactically} (i.e.~multiple occurrences of linear variables in the
program text), but ultimately preserve it in a \emph{semantic} sense,
%
where a linear term is still \emph{consumed exactly once} -- this is compounded
by lazy evaluation driving a non-trivial mismatch between syntactic and
semantic linearity.

\todo[inline]{Um exemplo ou dois para ilustrar o problema}

Therefore, the Core linear type-checker rejects various valid programs after
desugaring and optimizing transformations, because linearity is seemingly
violated.
%
The current solution to the linear type-checker rejecting valid programs is to effectively
disable the linear linter, since otherwise disabling optimisations can incur
significant performance costs.
%
However, we believe that GHC's transformations are correct, and it is the
linear type-checker and its underlying type system that cannot sufficiently
accommodate the resulting programs.

Additionally, some Core-to-Core transformations such as let-floating and
inlining already depend on linear type systems to produce more performant
programs. Valid linearity annotations in Core could potentially inform and
define more optimizations.

% TODO: Unnecessary
In Section~\ref{typingUsageEnvs} we describe usage environments and how they
solve three distinct problems. In Section~\ref{multiplicityCoercions} we discuss
the beginning of multiplicity coercions. In Section~\ref{examples} we take
programs that are currently rejected and show how the type system with our
extensions can accept them.

\section{Goals}

In the upcoming dissertation we will:

\begin{itemize}
\item Propose an extension of Core's type system and type checking algorithm
with additional linearity
information in order to accommodate linear programs in Core that
result from the optimising transformations described in Section~\ref{sec:ghcpipeline};
\item Argue the soundness of the resulting system (i.e.~no
  semantically non-linear programs are deemed linear);
\item Show how it validates Core-to-Core optimisation
  passes;
\item Implement the extension into GHC's Core type-checker (internally known as the Core linter).
\end{itemize}


\subsection{Extending Core's type system}

The key design goal of the extension of Core's type system is to
provide enough information so that seemingly syntactically
non-linear but semantically linear programs are equipped with enough
typing information so that they are deemed linearly well-typed, while
ruling out programs that violate linearity from being considered as
linearly typed.
%
To this end, we propose to extend Core's linear type system with
\emph{usage annotations} for let, letrec and case binder bound
variables\todo{dizer pq estes binders especificamente}. Given time, we will also explore a new kind of coercion for
multiplicities to validate programs that combine GADTs with
multiplicities.

\todo[inline]{Much of the work to account for linearity in Core with regard to
non-strict semantics of let-bindings might translate back to Haskell, though
the complexity of Haskell might make this quite hard}

\subsubsection{Usage Annotations / Typing Usage Environments}

\todo[inline]{Mover para aqui a parte do que sao as usage annotations
  e como funcionam. Acho que deves apresentar em 2 partes, uma e que
  se tivesses os usage envs bem calculados para tudo, resolvia
  problemas. Outra parte: calcular os usage environments e desafios
  associados. A tua abordagem passa entao por inferir os usage
  environments once and for all quando constrois um letrec, etc, e
  depois usar ``a regra''. Penso que nao precisas de apresentar os
  algoritmos em detalhe. Para apresentares regras, explica bem o que
  elas significam.}


\subsection{Validating the Work}

The ultimate measure of success is the \verb=-dlinear-core-lint= flag, which
activates and runs the linear type-checker after desugaring and each
Core-to-Core transformation. In its current implementation, enabling this flag
rejects many linearly valid programs. Ideally, by the end of our research and
implementation, this flag could be enabled by default and accommodate all
existing transformations. Realistically, we want to accept as many diverse
transformations as possible while still preserving linearity, even if we are
unable to account for all of them.

For each transformation we successfully support in our type system, we will
prove that it does indeed preserve linearity by type-checking the input program
to the transformation and the ouptut program.

Quantitively, we will benchmark the variation in compilation time and
heap-allocations when our extended type-checker is enabled, in comparison to
the compiler with the Core type-checker that ignores linearity annotations
being run.

The linear Core type-checker validation and benchmarks will be done by running
the GHC testsuite and compiling the \emph{head.hackage} package set
%
\footnote{\emph{head.hackage} is a package set comprised of relevant
libraries of the Haskell ecosystem which are compiled by, and patched against,
GHC's latest commit.}
%
with the \verb=-dlinear-core-lint= flag. The GHC project also automatically
runs tests and benchmarks through its continuous integration (CI) pipeline,
which we intend to use to further validate our implementation continuously.

% \todo[inline]{Falar um pouco de como tencionas validar o que
%   fazes. Diria que ha a validacao qualitativa obvia -- que
%   transformacoes podem agora ser linted ou nao, mas podera ser util
%   fazer alguma validacao mais quantitativa e ser util
% medir tempos de execucao de coisas (e.g.a construcao dos usage envs)}

\subsection{Tasks and Chronogram}

In the dissertation, we will propose an extension to Core / System $F_C$'s type
system and type-checking algorithm with additional linearity information (such
as \emph{usage environments}) in order to accommodate linear programs in Core
throughout the GHC pipeline (Section~\ref{sec:ghcpipeline}) stages of
desugaring and optimization. This type-system entails augmenting Core's syntax
to support additional linearity information and extending existing typing
judgments and rules to account for linearity.

Furthermore, the extended type-system must be proved to be sound, that is, our
type-system must provably not accept any programs which aren't linear. We will
prove the system to be sound using formal methods\todo{?}.

Because we want to ensure our type system validates programs before and after
optimizing transformations are applied, we will formally/informally validate
that each optimizing transformation does not destroy linearity in programs wrt
our type system.

We will implement this extension to Core in GHC, the leading Haskell compiler.
Core's type-system implementation, internally known as the Core linter, will
serve as the base for our extension. Running the Core linter will enforce an
iterative approach to implementing the extensions and allow us to validate our
progress continuously.

Defining and implementing this type-system in GHC can be done iteratively
because each binder can be handled separately. The typing rules for let
bindings, recursive let bindings, and case bindings are distinct, and
optimizing transformations seldom interact with all three at the same time.
%
Consequently, we can interweave the formal specification, implementation in
Core, and validation of individual optimizations and of our implementation.

Throughout this, we will write the final dissertation document, using it as a
driving force for the research which will cristalize our ideas and help
communicate them. GHC is a large project with many involved parties -- it is
crucial that we communicate our ideas and changes clearly, so we can benefit
from other contributor's expert feedback, and ultimately merge our changes to
Core upstream.


% \todo[inline]{Fazer uma ``expansao'' da lista itemizada que fiz antes mas com mais
% detalhe / passos, explicando numa frase ou duas o que cada tarefa e.
% Tens uma divisao natural em passos pelos varios binders, alternar com
% implementacao no GHC, etc. Nao esquecer de incluir a escrita do
% documento final!}


% to be able to preserve linearity accross the stages and to enable \emph{Lint} to
% preserve our sanity regarding linearity and eventually inform with linearity new
% transformations.

% A value allocated to be passed to a linear function and then never again used could
% bypass garbage collection.

% Our key innovation is that, by recognising join points as a language construct,
% we both preserve join points through subsequent transformations and exploit them
% to make those transformations more effective. Next, we formalize this ap-
% proach; subsequent sections develop the consequences.

\section{Typing Usage Environments\label{typingUsageEnvs}}

Haskell has call-by-need semantics that entail that an expression is not
evaluated when it is let-bound but rather when the binding variable is used.
This makes it challenging to reason about linearity for let-bound variables. The
following example fails to typecheck in Haskell, but semantically it is indeed
linear due to lazy evaluation:

\begin{code}
f :: a %1 -> a
f x = let y = x in y
\end{code}

Despite not being accepted by the surface-level language, linear programs using
lets occur naturally in Core due to optimising transformations that create let
bindings. In a similar fashion, programs which violate syntatic linearity
for other reasons other than let bindings are produced by Core transformations.

The solution we found to a handful of problems regarding binders is to have a
\emph{usage environment}. A usage environment is a mapping from variables to
multiplicities. The main idea is to annotate those binders with a usage
annotation rather than a multiplicity (in contrast, a lambda-bound variable has
exactly one multiplicity). When we find a bound variable with a usage
environment, we type linearity as if we were using all variables with
corresponding multiplicities from that usage environment.

In the above example, this would amount to annotating $y$ with a usage
environment $x := 1$ (because the expression bound by $y$ uses $x$ one time).
Upon using $y$, we are actually using $x$ one time, and therefore linearity is
preserved.

% The first set of problems appears in the core-to-core optimisation passes. GHC
% applies many optimising transformations to \emph{Core} and we believe those
% transformations preserve linearity. However, Core's linear type system cannot check
% that they indeed preserve linearity.

% The simpler examples come from straightforward and common optimising
% transformations. Then we have recursive let definitions that don't accommodate
% linearity even though it might converge to only use the value once. Finally, we
% have the empty case expression introduced with the \emph{EmptyCase} language
% extension that Core currently can't typecheck either.

% The key idea is to annotate every variable with either its multiplicity, if it's
% lambda bound, or with its usage environment, if it's let bound.

% A usage environment is a mapping from variables to multiplicities.

% When we lint a core expression, we get both its type and its usage environment.
% That means that to lint linearity in an expression, whenever we come across a
% free variable we compute its usage environment and take it into account

% TODO: When we type an expression we get both the type and usage environment

\subsection{Let}

Let bindings in Core are the first family of problems we tackle with usage
environment annotations. Multiple transformations can introduce let-bindings,
such as CSE and join points. By extending the type system to allow let-bindings in Core
we start paving the way to a linear linter.

Currently, every variable in Core is annotated with a multiplicity at its binding
site. The multiplicity for let-bound variables must be ignored throughout the
transformation pipeline or otherwise too many valid programs would be
rejected for violating linearity in its transformed type.

However, programs with let bindings can be correctly typed by associating a
usage environment to the bound variables. Instead of associating a multiplicity
to every binder, we want to associate a multiplicity if the variable is lambda
bound and a usage environment when it is let-bound. We then instantiate the usage
environment solution to lets in particular -- a let bound variable is annotated
with the usage environment computed from the binder expression; in the let body
expression, when we find an occurrence of the let bound variable we emit its
usage environment. The typing rule is the following:

\begin{mathparpagebreakable}
    \infer*[right=(let)]
    {\Gamma \vdash t : A \leadsto \{U\} \\
     \Gamma ; x :_{U} A \vdash u : C \leadsto \{V\}}
    {\Gamma \vdash \text{let } x :_{U} A = t \text{ in } u : C \leadsto \{V\}}
\end{mathparpagebreakable}

Take for example an expression in which $y$ and $z$ are lambda-bound with a
multiplicity of one. In the following code it might not appear as if $y$
and $z$ are both being consumed linearly, but indeed they are since in the first
branch we use $x$ -- which means using $y$ and $z$ linearly -- and we use $y$
and $z$ directly on the second branch. Note again that let binding $x$ doesn't
consume $y$ and $z$ because of lazy evaluation. Only \emph{using} $x$ consumes $y$ and
$z$.

\begin{code}
let x = (y, z) in
case e of
  Pat1 -> … x …
  Pat2 -> … y … z …
\end{code}

If we annotate the $x$ bound by the let with a usage environment $\delta$
mapping all free variables in its binder to a multiplicity ($\delta = [y := 1, z
:= 1]$), we could, upon finding $x$, simply emit that $y$ and $z$ are consumed
once. When typing the second branch we'd also see that $y$ and $z$ are used
exactly once. Because both branches use $y$ and $z$ linearly, the whole case
expression uses $y$ and $z$ linearly.

% Currently, in GHC, we don't annotate let-bound variables with a usage
% environment, but we already calculate a usage environment and use it to check
% some things (which things?)

% \begin{itemize}
%     \item occurrences? store usage environment in Ids (vars)
%     \item Recursive lets (can it be rewritten using fix)
%     \item Empty case expression
% \end{itemize}

% \subsection{Inlining}

% If we annotate the let bound variables with their usage and emit that usage when
% we come across those variables, we can solve the linearity issues with inlining.

\subsection{Recursive Lets}

A recursive let binds a variable to an expression that might use the bound
variable in its body. Certain optimisations can create a recursive let that uses
linearly bound variables in its binder body. We want to treat recursive lets
similarly to lets: attribute to bound variables a usage environment and emit it
when the variable is used.
% TODO: Replace "certain" with concrete examples

The challenging part about determining the usage environment of the variables bound
by a recursive let is knowing what usage to emit inside their own body, when
computing said usage environment. The example below uses $x$ linearly % \ref{example_letrec}
but how can we prove it? If we are able to somehow compute $f$'s usage
environment to $x := 1$, we know $x$ is used once when $f$ is applied to
$\mathit{True}$.

\begin{code}
letrec f = \case
        True -> f False
        False -> x
in f True
\end{code}

The key idea to computing the usage environment of multiple variables that use
themselves in their definition body is to perform the computation in two separate passes. First,
calculate a naive environment by emiting free variables multiplicities as usual
while treating the recursive-let bound variables as free ones. Second, pass the
variables names and their corresponding naive environment as input to
algorithm~\ref{computeRecUsages} to get a final usage environment. Intuitively,
the algorithm, for each recursive binder, iterates over all (initially naive) usage
environments and substitutes the recursive binder by the corresponding usage
environment, scaled up by the amount of times that recursive binder is used in
the environment being updated.

The algorithm for computing the usage environment of a set of
recursive definitions works as follows. An at least informal proof
that the algorithm is correct should eventually follow this.

\begin{itemize}
    \item Given a list of functions and their naive environment computed from
        the body and including the recursive function names ($(f, F), (g, G),
        (h, H)$ in which there might exist multiple occurrences of $f, g, h$ in $F, G, H$
    \item For each bound rec var and its environment, update all bindings and
        their usage as described in the algorithm
    \item After iterating through all bound rec vars, all usage environments
        will be free of recursive bind usages, and hence "final"
\end{itemize}

Note that the difficulty of calculating a usage environment for $n$
recursive-let bound variables increases quadratically, i.e. the algorithm has
$O(n^2)$ complexity, but this is not a problem since it's rare to have more than
a handful of binders in the same recursive let block.

% TODO: I should probably use the re-computed usageEnvs instead of the naiveUsageEnvs.
% I'm pretty sure it might fail in some inputs if I keep using the naiveUsageEnvs.
\begin{algorithm}
$usageEnvs \gets naiveUsageEnvs.map(fst)$\;
\For{$(bind, U) \in naiveUsageEnvs$}{
    \For{$V \in usageEnvs$}{
        $V \gets sup(V[bind]*U\setminus\{bind\}, V\setminus\{bind\})$
    }
}
\caption{computeRecUsages\label{computeRecUsages}}
\end{algorithm}

Putting the usage environment idea together with the algorithm we obtain the following typing rule:

\begin{mathparpagebreakable}
    \infer*[right=(letrec)]
    {\Gamma ; x_1 : A_1 \dots x_n : A_n \vdash t_i : A_i \leadsto \{U_{i_\text{naive}}\} \\
     (U_1 \dots U_n) = \mathit{computeRecUsages}(U_{1_\text{naive}} \dots U_{n_\text{naive}}) \\
     \Gamma ; x_1 :_{U_1} A_1 \dots x_n :_{U_n} A_n \vdash u : C \leadsto \{V\}}
    {\Gamma \vdash \text{let } x_1 :_{U_1} A_1 = t_1 \dots x_n :_{U_n} A_n = t_n \text{ in } u : C \leadsto \{V\}}
\end{mathparpagebreakable}

Instantiating the usage environment solution according to the above description,
here's an informal proof that the previous example is well typed: We %\ref{example_letrec}
compute the naive usage environment of $f$ to be $x := 1, f := 1$. We compute
its actual usage environment by scaling the naive environment of $f$ without $f$
by the amount of times $f$ appears in the naive environment of $f$ ($1*[x :=
1]$) and get $x := 1$. Finally, we emit $x := 1$ from applying $f$ in the let's
body.

% Following the idea of making let-bound variables remember the usage environment
% here's an informal description that that example is well typed. We want to
% anotate the let-bound variable $f$ with a usage environment delta $\delta$, and
% use the binding body to compute it.

% Description of computing usage environment of a case expression:
% https://gitlab.haskell.org/ghc/ghc/-/wikis/uploads/355cd9a03291a852a518b0cb42f960b4/minicore.pdf.

% However, not understanding it, my take would be that we can compute the usage
% environment of every branch of the case expression and make sure that they all
% unify (wrt to submultiplicities). The special case is when the branch happens to
% call $f$ itself while computing the usage environment of $f$. If it were another
% let bound variable we'd add its own usage environment to the one we're
% computing; if it were a lambda bound variable we'd add [itself $:=$ its
% multiplicity].

% My idea is that we can emit a special usage [$rec := p$], which, when unified
% against the other case branches $\delta$ will always succeed with a unification
% mapping from $rec \rightarrow p\delta$ scaled by the multiplicity of $rec$

% So taking the example, to compute the usage environment of $f$, we'd compute for
% the second branch $[x := 1]$ and for the first branch $[rec := 1]$. Then, we'd
% unify them with $rec \rightarrow [x := 1*1]$, and somehow result in $[x := 1]$

The next example is a linearly invalid program because $x$ is a %~\ref{example_letrec_2}
linearly bound variable that is used more than once, and shows how this method
correctly rejects it.

\begin{code}
letrec f = \case
         True -> f False + f False
         False -> x
    in f True
\end{code}

To compute the usage environment of $f$ we take its naive environment to be $x
:= 1, f := 2$. Then, we compute the final environment to be $x := 1$ scaled by
the usage of $f$, $2*[x := 1]$, resulting in $x := 2$. Now, to lint the
linearity of the whole let we must ensure the body of the let uses $x$ linearly.
We emit from the body the usage environment of $f$ ($x := 2$) which uses $x$
more than once, i.e. not linearly.

% To compute the usage environment of $f$ we take the second branch usage
% environment $[x := 1]$ and the first branch usage $[rec := 1+1]$ and unify them,
% somehow resulting in $[x := 2]$. Now, to lint the linearity in the whole let
% expression we must ensure that the body of the let uses $x$ linearly. The body
% is $f True$, which is a let-bound variable (how to distinguish functions that
% must be applied vs variables) so we take its usage environment $[x := 2]$ which
% does not use $x$ linearly and thus breaks linearity.

% \textbf{Re-explained:} to compute the usage environment of the recursive
% let-bound function $f$ when applied, we compute $Z$ such that for all branch
% alternatives $U,V,...$, $U \subset Z$, $V \subset Z$ and so on by tracking the
% multiplicities and usage environments of variables that show up in the body and
% by emitting a special keyword $rec$ everytime we find a saturated call of $f$
% (how to handle unsaturated calls?) (how to have a more general solution that
% doesn't require a keyword, perhaps something to do with fixed points); Then we
% scale $Z \setminus \{(rec,_)\}$ by $Z[rec]$ and get $T$ which is the usage
% environment of $f$ when saturated.

% \textbf{Example 1 revisited:}
% \begin{enumerate}
%     \item Take $U = \{rec := 1\}$
%     \item Take $V = \{x := 1\}$
%     \item Take $Z = \{x := 1, rec := 1\}$
%     \item Take $\pi = Z[rec] = 1$
%     \item Take $W = Z \setminus \{rec\} = \{x := 1\}$
%     \item Take $T = \pi W = \{x := \pi * 1\} = \{x := 1\}$
%     \item Linearity OK
% \end{enumerate}

% \textbf{Example 2 revisited:}
% \begin{enumerate}
%     \item Take $U = \{rec := 2\}$
%     \item Take $V = \{x := 1\}$
%     \item Take $Z = \{x := 1, rec := 1\}$
%     \item Take $\pi = Z[rec] = 2$
%     \item Take $W = Z \setminus \{rec\} = \{x := 1\}$
%     \item Take $T = \pi W = \{x := \pi * 1\} = \{x := 2\}$
%     \item Linearity not OK
% \end{enumerate}


% Draft typing rule:

% In haskell that would look like this;
% \begin{code}
% computeRecUsageEnvs :: [(Var, UsageEnv)] -- Recursive usage environments associated to their recursive call
%                     -> [(Var, UsageEnv)] -- Non-recursive usage environments
% computeRecUsageEnvs l =
%   foldl (flip \\(v,vEnv) -> map \\(n, nEnv) -> (n, ((fromMaybe 0 \$ v `M.lookup` nEnv) `scale` (M.delete v vEnv)) `sup` (M.delete v nEnv))) l l

% sup :: UsageEnv -> UsageEnv -> UsageEnv
% sup = M.merge M.preserveMissing M.preserveMissing (M.zipWithMatched \$ \_ x y -> max x y)

% scale :: Mult -> UsageEnv -> UsageEnv
% scale m = M.map (*m)
% \end{code}

\subsection{Handling the case binder\label{casebinder}}

% (though in the rule seems to only start counting after the second usage which
% would make the rule wrong for a case expression that doesn't use the binder --
% the scrutinee should also be consumed)
The current typing rule for case expressions describes that using the case
binder is as using the case scrutinee multiple times, so we scale the usage of
the case scrutinee by the superior multiplicity of using the case binder across
all branches. However, we hypothetize that this prevents us from typing many
valid programs and ultimately does not correctly capture the usage of a
variable and present a seemingly viable alternative.

Firstly, we recall the definition of \emph{consuming a value} from Linear
Haskell as
\begin{itemize}
    \item Consuming an atomic value is forcing it to Normal Form (NF)
    \item Consuming a value that is constructed with more than 1 argument is
        consuming all of its arguments
\end{itemize}
and further note that when an expression is scrutinized by a case expression it
is evaluated to Weak Head Normal Form (WHNF), which in the case of a nullary data
constructor is equal to NF.

Now, with the following example, my interpretation of the current rule dictates
that the case expression consumes the scrutinee twice because the case binder is
used. However, we know that in the branch where $z$ is used, $z$ is equal to
False, and using False does not violate linearity since we can unrestrictedly
create nullary data constructors. A situation similar to this one below happens
after the CSE transformation.
\begin{code}
    case <complex expression> of z {
        False -> case y of z' { DEFAULT -> z }
        True  -> y
    }
\end{code}
% $\leadsto U$ 

A different example is using the case binder $z$ instead of the arguments we
pattern matched on $x,y$. This currently violates linearity because both $x$ and
$y$ aren't used and because $z$ is used twice. This doesn't typecheck in the
frontend either. However, we know that in this branch, using $z$ is effectively
the same as using $(x,y)$!
\begin{code}
    case <complex expression> of z {
        (x,y) -> z
    }
\end{code}
% $\leadsto U$ 

The good news is that both these programs (and a handful of others listed in
Section~\ref{examples}) are accepted with a new rule we have devised for the
linear linter. We still need to prove we don't accept any invalid programs as
valid.

The key idea of the case-binder-usage solution is \textbf{annotating the case binder
with independent usage environments for each pattern match}. That is, for
each of the possible branches, using the case binder $z$ will equate to
using its usage environment in that branch. That makes it so that using the
case binder instead of a nullary data constructor is the same, using the case
binder instead of reconstructing the value with the bound pattern variables too,
and other situations in which we previously couldn't typecheck linearity are
now accepted.

The typing rule for the case expression using the case binder solution:

\begin{mathparpagebreakable}
    \infer*[right=(case)]
    {\Gamma \vdash t : D_{\pi_1 \dots \pi_n} \leadsto \{U\} \\
     \Gamma ; z :_{U_k} D_{\pi_1 \dots \pi_n} \vdash b_k : C \leadsto \{V_k\}
     \and V_k \leq V}
    {\Gamma \vdash \text{case } t \text{ of } z :_{(U_1\dots U_n)} D_{\pi_1 \dots \pi_n} \{b_k\}_1^m : C \leadsto \{U + V\}}
\end{mathparpagebreakable}

Taking the first example in this section, we annotate both branches (True and
False) with $U_z = \emptyset$ because the pattern match doesn't introduce any
new variables. We consume \emph{complex expression} once and $y$ once, and then use
$z$ once. However, using $z$ once equates to not using anything (semantically
this relates to being able to use False or True unrestrictedly) and therefore
linearity is preserved.

In the second example, we know annotate the only branch with usage environment
$U_z = [x := 1, y := 1]$. Upon the usage of $z$ we emit $x$ and $y$ --
effectively using both -- thus linearity is preserved.

\section{Multiplicity Coercions\label{multiplicityCoercions}}

The second set of problems arises from our inability to coerce a multiplicity
into another (or say that one is submultiple of another?).

% When we pattern match on a GADT we ...

Taking the following example we can see that we don't know how to say
that x is indeed linear in one case and unrestricted in the other, even though
it is according to its type. We'd need some sort of coercion to coerce through
the multiplicity to the new one we uncover when we pattern match on the GADT
evidence (...)

\begin{code}
data SBool :: Bool -> Type where
  STrue :: SBool True
  SFalse :: SBool False

type family If b t f where
  If True t _ = t
  If False _ f = f

dep :: SBool b -> Int %(If b One Many) -> Int
dep STrue x = x
dep SFalse _ = 0
\end{code}


% \section{Novel rules}

% \subsection{The usage environment in a Recursive Let}

% \subsection{The usage environment of a Case Binder\label{caseBinderKey}}


% \begin{mathparpagebreakable}
%     \infer*[right=(letrec)]
%     {\Gamma ; \Delta/ \Delta' ; \Omega \vdash M : A \Uparrow \and \Gamma ;
%     \Delta/ \Delta'' ; \Omega \vdash N : B \Uparrow \and \Delta' = \Delta''}
%     {\Gamma ; \Delta/\Delta' ; \Omega \vdash  (M \with N) : A \leadsto U}
% \end{mathparpagebreakable}


\section{Examples\label{examples}}

In this section we present worked examples of programs that currently fail to
compile with \textbf{-dlinear-core-lint} but would succeed according to the
novel typing rules we introduced above. Each example belongs to a subsection
that indicates after which transformation the linting failed.

\subsection{After the desugarer (before optimizations)}

The definition for $\$!$ in \textbf{linear-base}\cite{linearbase} fails to lint after the
desugarer (before any optimisation takes place) with \emph{Linearity failure in
lambda: x 'Many $\not\subseteq$ p}
\begin{code}
($!) :: forall {rep} a (b :: TYPE rep) p q. (a %p -> b) %q -> a %p -> b
($!) f !x = f x
\end{code}

The desugared version of that function follows below. It violates (naive?)
linearity by using $x$ twice, once to force the value and a second time to call
$f$. However, the $x$ passed as an argument is actually the case binder and it
must be handled in its own way. The case binder is the key (as seen
in~\ref{casebinder}) to solving this
and many other examples.
\begin{code}
($!)
  :: forall {rep :: RuntimeRep} a (b :: TYPE rep) (p :: Multiplicity)
            (q :: Multiplicity).
     (a %p -> b) %q -> a %p -> b
($!)
  = \ (@(rep :: RuntimeRep))
      (@a)
      (@(b :: TYPE rep))
      (@(p :: Multiplicity))
      (@(q :: Multiplicity))
      (f :: a %p -> b)
      (x :: a) ->
      case x of x { __DEFAULT -> f x }
\end{code}

% Intuitively, this program is linear because forcing the polymorphic value to
% WHNF ...? Need better semantics of consuming
%
The case binder usage rule typechecks this program because $x$ is consumed once,
the usage environment of the case binder is empty ($x :_\emptyset a$) and,
therefore, when $x$ is used in $f(x)$, we use its usage environment which is
empty, so we don't use anything new.

\emph{How are strictness annotations typed in the frontend? The issue is this program
consumes to value once to force it, and then again to determine the return
value.}

% Work better the meaning of consumption (does it mean for a value to be reduced
% to WHNF?). Is consuming = forcing? Why is the above program linear?

As a finishing note on this example, we show the resulting program from
\textbf{-ddump-simpl} that simply uses a different name for the case binder.
\begin{code}
($!)
  :: forall {rep :: RuntimeRep} a (b :: TYPE rep)
            (p :: Multiplicity) (q :: Multiplicity).
     (a %p -> b) %q -> a %p -> b
($!)
  = \ (@(rep :: RuntimeRep))
      (@a)
      (@(b :: TYPE rep_aSJ))
      (@(p :: Multiplicity))
      (@(q :: Multiplicity))
      (f :: a %p -> b)
      (x :: a) ->
      case x of y { __DEFAULT -> f_aDV y }
\end{code}
% So in this program we use another name for the case binder, but it still stands
% for the resulting of evaluating to WHNF; how is it technically different?

\subsection{Common Sub-expression Elimination}

Currently, the CSE seems to transform a linear program that pattern matches on
constant and returns the same constant into a program that breaks linearity that
pattern matches on the argument and returns the argument (where in the frontend
a constant equal to the argument would be returned)

The definition for $\&\&$ in \textbf{linear-base} fails to lint after the common
sub-expression elimination (CSE) pass transforms the program.
\begin{code}
(&&) :: Bool %1 -> Bool %1 -> Bool
False && False = False
False && True = False
True && x = x
\end{code}
The issue with the program resulting from the transformation is $x$ being used
twice in the first branch of the first case expression. We pattern match on y to
force it (since it's a type without constructor arguments, forcing is consuming)
and then return $x$ rather than the constant $False$
\begin{code}
(&&) :: Bool %1 -> Bool %1 -> Bool
(&&) = \ (x :: Bool) (y :: Bool) ->
  case x of w1 {
    False -> case y of w2 { __DEFAULT -> x };
    True -> y
  }
\end{code}
At a first glance, the resulting program is impossible to typecheck linearly.

The key observation is that after $x$ is forced into either $True$ or $False$,
we know $x$ to be a constructor without arguments (which can be created
without restrictions) and know that where we see $x$ we can as well have
$True$ or $False$ depending on the branch. However, using $x$ here is very
unsatisfactory (and linearly unsound?) because $x$ might be an expression, and
we can't really associate $x$ to the value we pattern matched on (be it $True$
or $False$). What we really want to have instead of $x$ is the $w1$ case binder --
it relates directly to the value we pattern matched on, it's a variable rather
than an expression, and, most importantly, our case-binder-usage idea could be
applied here as well

% Idea: if $x$ was anotated with some information regarding the CSE then perhaps
% it could be typechecked (in a system that considered said anotations) -- This is
% too specific and the case binder environment solution is much cleaner. It just
% requires that the example is changed into using the case binder $w1$ rather than
% $x$.

The solution with the unifying case binder usage idea means annotating the case
binder with its usage environment. For $True$ and $False$ (and other data
constructors without arguments) the usage environment is always empty (using
them doesn't entail using any other variable), meaning we can always use the
case binder instead of the actual constant constructor without issues.
%
Concretely, if we had $w1$ instead of the second occurrence of $x$, we'd have
an empty usage environment for $w1$ in the $False$ branch ($w1 :_\emptyset
Bool$) and upon using $w1$ we wouldn't use any extra resources


To make this work, we'd have to look at the current transformations and see
whether it would be possible to ensure that CSEing the case scrutinee would
entail using the case binder instead of the scrutinee. I don't know of a
situation in which we'd really want the scrutinee rather than the case binder,
so I hypothetize the modified transformation would work out in practice and
solve this linearity issue.


% In this exact example, the binder has usage environment empty ($w1 := []$),
% meaning that in the False branch, when we use $x$, if we instead used $w1$ which
% is equivalent and seems more correct (since it doesn't need the case scrutinee
% expression to be a variable), then the usage of $w1$ would imply the usage of
% $[]$ which is nothing and therefore we would preserve linearity

Curiously, the optimised program resulting from running all transformations
actually does what we expected it with regard to using the constant constructors
and preserving linearity. So is the issue from running linear lint after a
particular CSE but it would be fine in the end?
\begin{code}
(&&) :: Bool %1 -> Bool %1 -> Bool
(&&) = \ (x :: Bool) (y :: Bool) ->
  case x of {
    False -> case y of { __DEFAULT -> GHC.Types.False };
    True -> y
  }
\end{code}

\subsection{Compiling ghc with -dlinear-core-lint}

From the definition of $\mathit{groupBy}$ in $\mathit{GHC.Data.List.Infinite}$:

\begin{code}
groupBy :: (a -> a -> Bool) -> Infinite a -> Infinite (NonEmpty a)
groupBy eq = go
  where
    go (Inf a as) = Inf (a:|bs) (go cs)
      where (bs, cs) = span (eq a) as
\end{code}

We get a somewhat large resulting core expression, in the middle of which the
following expression with a linear type -- which currently syntatically violates
linearity.

\begin{code}
jp :: ([a], Infinite a) \%1 -> (# [a], Infinite a #)
jp (wwj :: ([a], Infinite a)) =
    case wwj of wwj {
        DEFAULT -> case wwj of { (wA, wB) -> (# wA, wB #) }
    }
\end{code}

Using the case binder usage solution, the case binder is annotated with a usage
environment for the only branch ($U_wwj = \emptyset$) and using $wwj$ is equal
to using the $\emptyset$. Here it would mean that second \textbf{case of} $wwj$
doesn't actually use any variables and hence the first $wwj$ isn't used twice.


% \begin{code}
% groupBy = \ (@a) (eq :: a -> a -> Bool) (eta :: Infinite a) ->
%   letrec {
%     go :: Infinite a -> Infinite (NonEmpty a)
%     go = \ (inf :: Infinite a) -> case inf of {
%       Inf x xs -> let {
%         ds :: ([a], Infinite a)
%         ds = let {
%             parteq :: a -> Bool
%             parteq = eq x
%         } in
%           letrec {
%             goZ :: Infinite a -> ([a], Infinite a)
%             goZ = \ (inf' :: Infinite a) -> case wgo inf' of { (# wA, wB #) -> (wA, wB) };

%             wgo :: Infinite a -> (# [a], Infinite a #)
%             wgo = \ (inf' :: Infinite a) -> case inf' of wildX2 {
%               Inf y ys ->
%                 join {
%                     jp :: ([a], Infinite a) \%1 -> (# [a], Infinite a #)
%                     jp (wwj :: ([a], Infinite a)) =
%                         case wwj of wwj {
%                             DEFAULT -> case wwj of { (wA, wB) -> (# wA, wB #) } }
%                     } in
%                       case parteq y of {
%                         False ->
%                             let {
%                                 ww :: ([a], Infinite a)
%                                 ww = ([] @a, wildX2)
%                             } in jump jp ww;
%                         True ->
%                             let {
%                                 dy :: ([a], Infinite a)
%                                 dy = case wgo ys of { (# wA, wB #) -> (wA, wB)
%                                 }
%                             } in
%                                 let {
%                                     wwB :: [a]
%                                     wwB = case dy of { (bs, cs) -> bs }
%                                 } in
%                                     let {
%                                         wwA :: [a]
%                                         wwA = : @a y wwB
%                                     } in let {
%                                         wwC :: Infinite a
%                                         wwC = case dy of { (bs, cs) -> cs }
%                                     } in let {
%                                         ww :: ([a], Infinite a)
%                                         ww = (wwA, wwC)
%                                     } in jump jp ww
%                                 }
%               };
%           } in
%               case wgo xs of { (# wA, wB #) -> (wA, wB) }
%       } in
%           Inf @(NonEmpty a) (:| @a x (case ds of { (bs, cs) -> bs })) (case ds of { (bs, cs) -> go cs })
%     };
%   } in go eta
% \end{code}
% The issue is in the linear function that shows up in the core output (how does
% the linearity end up there?). The wwj variable is used once in the case
% expression, bound as the case binder, and used in the case body once again. Why
% do we do that instead of pattern matching right away? Seems a bit redundant.

% Observation: If the branch is DEFAULT, then the case binder binds the case
% scrutinee which was just forced?, but hasn't been actually consumed, because we
% haven't consumed its components. As long as the same branch doesn't consume the
% pattern matching result and the case binder at the same time it should be fine?

% In this example, we force wwj with the case binder, but we don't really
% consume it (more precise definition of consume...), so we can use the case
% binder meaning we're simply using x for the first time. Needs to be
% formalised....


\subsection{Artificial examples}

Following the difficulties in consuming or not consuming the case binder and its
associated bound variables linearly we constructed some additional examples that
bring out the problem quite clearly.
\begin{code}
case x of w1
    (x1,x2) -> case y:Bool of
                DEFAULT -> (x1,x2)
\end{code}
Is equal to (note that the case binder is being used rather than the $x$ case
scrutinee which could be an arbitrary expression and hence really cannot be
consumed multiple times?)
\begin{code}
case x of w1
    (x1,x2) -> case y:Bool of
                DEFAULT -> w1
\end{code}

We initially wondered whether x was being consumed if the pattern match ignored
some of its variables. We pose that if it does have wildcards then it isn't
consuming x fully
\begin{code}
case x of w1
    (_,x2) -> Is x being consumed? no because not all of its components are
    being consumed?
\end{code}

Can we have a solution that even handles weird cases in which we pattern match
twice on the same expression but only on one constructor argument per time? I
don't think so.
\begin{code}
case exp of w1
    (x1,_) -> case w1 of w2
                (_, x2) -> (x1, x2)
\end{code}

A double let rec in which both use a linear bound variable $y$
\begin{code}
letrec f = \case
        True  -> y
        False -> g True
       g = \case
        True -> f True
        False -> y
    in f False
\end{code}

We have to compute the usage environment of f and g.
For f, we have the first branch with usage environment $y$ and the second with
usage $g$, meaning we have $F = \{g := 1, y := 1\}$
For g, we have $G = \{f := 1, y := 1\}$. To calculate the usage environment of
$f$ to emit upon $f False$, we calculate ...

Refer to the algorithm for computing recursive environment


% \section{Work in progress}

% % \section{Core to Core Validation}
% \subsection{Inlining}

% \subsection{CSE}

% \subsection{Join Points}

% When duplicating a case (in the case-of-case transformation), to avoid code
% explosion, the branches of the case are first made into join points

% \begin{code}
% case e of
%   Pat1 -> u
%   Pat2 -> v
% ~~>
% let j1 = u in
% let j2 = v in
% case e of
%   Pat1 -> j1
%   Pat2 -> j2
% \end{code}

% If there is any linear variable in u and v, then the standard
% let rule above will fail (since j1 occurs only in one branch, and
% so does j2).

% However, if j1 and j2 were annotated with their usage environment,

% \subsection{Empty Case}

% For case expressions, the usage environment is computed by checking all branches
% and taking sup. However, this trick doesn't work when there are no branches.

% \begin{itemize}
% \item https://gitlab.haskell.org/ghc/ghc/-/issues/20058
% \item https://gitlab.haskell.org/ghc/ghc/-/issues/18768

% \item (1) Just like a case expression remembers its type (Note [Why does Case have a
% 'Type' field?] in Core.hs), it should remember its usage environment. This data
% should be verified by Lint.

% \item (2) Once this is done, we can remove the Bottom usage and the second field of
% UsageEnv. In this step, we have to infer the correct usage environment for empty
% case in the typechecker.
% \end{itemize}

% \begin{code}
% {-# LANGUAGE LinearTypes, EmptyCase #-}
% module M where

% {-# NOINLINE f #-}
% f :: a %1-> ()
% f x = case () of {}
% \end{code}

% This example is well typed: a function is linear if it consumes its argument
% exactly once when it's consumed exactly once. It seems like the function isn't
% linear since it won't consume x because of the empty case, however, that also
% means f won't be consumed due to the same empty case, thus linearity is
% preserved.

% \begin{code}
% * In the case of empty types (see Note [Bottoming expressions]), say
%   data T
% we do NOT want to replace
%   case (x::T) of Bool {}   -->   error Bool "Inaccessible case"
% because x might raise an exception, and *that*'s what we want to see!
% (#6067 is an example.) To preserve semantics we'd have to say
%    x `seq` error Bool "Inaccessible case"
% but the 'seq' is just such a case, so we are back to square 1.
% \end{code}

% There are three different problems:

% \begin{itemize}
% \item castBottomExpr converts (case x :: T of {}) :: T to x.
% \item Worker/wrapper moves the empty case to a separate binding
% \item CorePrep eliminates empty case, just like point 1 (See -- Eliminate empty
%     case in GHC.CoreToStg.Prep
% \end{itemize}

% With castBottomExpr, we get the example above to
% \begin{code}
%     f = \ @a (x (%1) :: a) -> ()
% \end{code}
% And if we don't, 
% \begin{code}
%     f = \ @a (x (%1) :: a) -> case () of {}
% \end{code}
% And that supposedly if we had a usage environment in the case expression we
% could avoid the error. How is it typed without the transformation in face
% of the bottom? (Even knowing that theoretically it's because of divergence?)