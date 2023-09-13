%include polycode.fmt
%format ⊸ = "\lolli"

% Needed in order of creation because of the new vs renew commands
\input{proof}
\input{language-v2/proof}
\input{language-v3/proof}
\input{language-v4/proof}
\input{language-v4/Syntax}
\input{language-v4/TypingRules}
\input{language-v4/TheoremsAndLemmas}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% {{{ Chapter: A Type System for Semantic Linearity in Core; Introduction
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{A Type System for Semantic Linearity in Core}

\begin{itemize}

\item A linear type system statically guarantees that linear resources are consumed
\emph{exactly once}.
\item With linear types, programmers can create powerful abstractions that enforce
certain resources to be used linearly, such as file handles or allocated
memory.

\item Linear Haskell brings the promises of linear types to the Haskell, and is
available in the Glasgow Haskell Compiler (GHC) starting from version 9.0.

\item For example: trivial linear haskell program

\item GHC desugars Linear Haskell into an intermediate language called Core, a
System FC, and then applies multiple so-called Core-to-Core optimising
transformations in succession.

\item For example: some simple inlining

\item Linear functions are likewise optimised by the compiler but, crucially,
the optimisations must preserve linearity! It would indeed be disastrous if the
compiler discarded or duplicated resources such as a file handle or some allocated memory.

\item From the above example, consider |x| linear. It might seem as though |x|
is being used twice, but since Core's evaluation strategy is call-by-need, we
will only evaluate the let when the value is required, and since after
optimisation it is never used, we'll never compute the value and thus never use the resource

\item In essence, in a lazy language such as Haskell, there's a mismatch
between syntactic and semantic linearity, with the former referring to
syntactic occurrences of a linear resource in the program text, and the latter
to whether the program consumes the resource exactly once in a semantic sense,
accounting for the evaluation strategy such as in the let example above.

\item The problem: Core is not aware of this. Its linear type system is still
very naive, in that it doesn't understand semantic linearity, and will reject
most transformed linear programs, since often transformations turn programs
that are syntactically linear to programs that are only semantically linear.

\item Despite using Core's type system to validate the implementation
of the optimising transformations preserve types (and all their combinations),
we don't use the Core's linear type system to validate whether the
optimisations and their implementation preserves \emph{linearity}. We
only \emph{think} that the current optimisations preserve linearity, but we
don't check it.

\item Understanding semantic linearity isn't trivial, and, in fact, we aren't
aware of any linear type system that accounts for non-strict evaluation
semantics besides our own.

\item We develop a linear type system for Core that understands semantic
linearity. We prove the usual preservation and progress theorems with it, and
then prove that multiple optimisations preserve types With it, we can accept
all intermediate programs GHC produces while applying Core-to-core optimising
transformations.

\item We implemented a GHC plugin that validates every Core program produced by
the optimising pipeline using our type system

\item Contributions (ref section for each):
\begin{itemize}
\item We explain and build intuition for semantic linearity in Core programs by example
\item We present a linear type system for call-by-need Core which understands
all axis of semantic linearity we previously exposed; and we prove type
safety of that system
\item We prove that multiple Core-to-core optimising transformations preserve linearity +
types under the type system; and discuss 
\item We develop a GHC plugin that checks all intermediate Core programs using
our type system
\end{itemize}

\end{itemize}

\todo[inline]{The introduction needs a lot of motivation!}

\todo[inline]{
    Inicío deve motivar o leitor, e temos de explicar qual é o problema da
    linearidade sintatica em Haskell (vs semantica), e a interação disso com o
    call-by-need/lazy evaluation. Quase como se fosse um paper.
}

\todo[inline]{Compiler optimizations put programs in a state where linearity
mixed with call-by-need is pushed to the limits. That is, the compiler
preserves linearity, but in a non-trivial semantic way.}

\todo[inline]{We present a system that can understand linearity in the presence
of lazy evaluation, and validate multiple GHC core-to-core optimizations in
this system, showing they can preserve types in our system where in the current
implemented Core type system they don't preserve linearity.}

\todo[inline]{Note that programmers won't often write these programs in which
let binders are unused, or where we pattern match on a known constructor -- but
these situations happen all the time in the intermediate representation of an
optimising compiler $\dots$}

% ROMES:TODO:
%Since the publication of Linear Haskell~\cite{cite:linearhaskell} and its
%implementation in GHC 9.0, Haskell's type system supports linearity annotations
%in functions. Linear Haskell effectively brings linear types to a mainstream,
%pure, and lazy functional language. Concretely, Haskell function types can be
%annotated with a multiplicity, where a multiplicity of \texttt{1} requires the
%argument to be consumed exactly once and a multiplicity of \texttt{Many} allows
%the function argument to be consumed unrestrictedly, i.e., zero or more times.
%
%% A function is linear if it consumes its arguments exactly once when it itself
%% is consumed exactly once.
%
%As mentioned in Section~\ref{sec:core}, GHC Haskell features two typed
%languages in its pipeline: Haskell and its main intermediate language, Core
%%
%(Core is a much smaller language than the whole of Haskell, even though we can
%compile the whole of Haskell to Core).
%%
%The addition of linear types to
%GHC Haskell required changing the type system of both languages. However,
%Linear Haskell only describes an extension to the surface-level Haskell type
%system, not Core. Nonetheless, in practice, Core is linearity-aware.
%
%We want Core and its type system to give us guarantees about desugaring and
%optimizing transformations with regard to linearity just as Core does for types
%-- a linearly typed Core ensures that linearly-typed programs remain correct
%both after desugaring and across all GHC optimizing transformations,
%i.e.~linearity is preserved when desugaring and optimisations should not
%destroy linearity.
%
%% \todo[inline]{Nao e necessario reexplicar o que e o Core, o que e
%%   preciso aqui e explicar que o desugaring tem anotacoes de
%%   linearidade mas que sao ignoradas e explicar porque. Em particular,
%%   algum do texto que esta mais a frente a dizer as variaveis sao
%%   anotadas no Core mas que e tudo ignorado deve ficar claro nesta altura}
%
%% This type
%% checker (called \emph{Lint}) gives us guarantees of correctness in face of all
%% the complex transformations a Haskell program undergoes, such as desugaring and
%% core-to-core optimization passes, because the linter is always run on the resulting code
%% before ultimately being compiled to (untyped) machine code.
%
%% System FC is the formal system in which the implementation of GHC's intermediate
%% representation language \emph{Core} is based on.
%
%
%Core is already annotated with linearity, but its type-checker \textbf{currently ignores linearity annotations}.
%%
%In spite of the strong formal foundations of linear types driving the
%implementation, their interaction with the whole of GHC is still far from
%trivial. The implemented type system cannot accomodate several optimising
%transformations that produce programs which violate linearity
%\emph{syntactically} (i.e.~multiple occurrences of linear variables in the
%program text), but ultimately preserve it in a \emph{semantic} sense,
%%
%where a linear term is still \emph{consumed exactly once} -- this is compounded
%by lazy evaluation driving a non-trivial mismatch between syntactic and
%semantic linearity.
%
%\todo[inline]{Expand a bit on call-by-need vs call-by-value linearity. How can
%we make this a bigger part of our work and introduction?}
%
%Consider the example in Figure~\ref{fig:first-motivation}, an expression in which
%$y$ and $z$ are variables bound by a $\lambda$-abstraction, and both are
%annotated with a multiplicity of \texttt{1}. Note that let-binding $x$ doesn't
%necessarily consume $y$ and $z$ because of Core's call-by-need semantics.
%%
%\begin{figure}[h]
%  \begin{minipage}[l]{0.49\textwidth}
%    \begin{code}
%    let x = (y, z) in
%    case e of
%      Pat1 -> … x …
%      Pat2 -> … y … z …
%    \end{code}
%  \end{minipage}
%  \begin{minipage}[r]{0.49\textwidth}
%    \caption{Example Inlining}
%  \end{minipage}
%\label{fig:first-motivation}
%\end{figure}
%%
%In the example, it might not seem as though $y$ and $z$ are both being
%consumed linearly but, in fact, they both are. Given that in the first branch
%we use $x$ -- which entails using $y$ and $z$ linearly -- and in the second
%branch we use $y$ and $z$ directly, in both branches we are consuming both $y$
%and $z$ linearly.
%
%% TODO:HELP: Fix links to motivation-2 showing up as links to motivation-1
%Similarly, consider the program in Figure~\ref{fig:second-motivation} with a
%let-binding that uses $x$, a linearly bound $\lambda$-variable. In surface
%level Haskell, let-bindings always consume linear variables \texttt{Many} times
%to avoid dealing with the complexity of call-by-need semantics, so this program
%would not type-check, because $x$ is being consumed \texttt{Many} times instead
%of \texttt{1}.
%%
%\begin{figure}[h]
%  \begin{minipage}[l]{0.49\textwidth}
%    \begin{code}
%    f :: a %1 -> a
%    f x = let y = x+2 in y
%    \end{code}
%  \end{minipage}
%  \begin{minipage}[r]{0.49\textwidth}
%    \caption{Example Let}
%  \end{minipage}
%\label{fig:second-motivation}
%\end{figure}
%%
%Despite not being accepted by the surface-level language, linear programs using
%lets occur naturally in Core due to optimising transformations that create let
%bindings, such as $\beta$-reduction. In a similar fashion, programs which
%violate syntactic linearity for other reasons other than let bindings are
%produced by Core transformations.
%
%% Therefore, the Core linear type-checker rejects various valid programs after
%% desugaring and optimizing transformations, because linearity is seemingly
%% violated.
%%
%The current solution to valid programs being rejected by Core's linear
%type-checker is to effectively disable the linear type-checker since,
%alternatively, disabling optimizing transformations which violate linearity
%incurs significant performance costs.
%%
%However, we believe that GHC's transformations are correct, and it is the
%linear type-checker and its underlying type system that cannot sufficiently
%accommodate the resulting programs.
%
%Additionally, some Core-to-Core transformations such as let-floating and
%inlining already depend on custom linear type systems to produce more
%performant programs. Valid linearity annotations in Core could potentially
%inform and define more optimizations.

\todo[inline]{Continue introduction}

Our contributions are (to rewrite):
\begin{itemize}
\item We expose a connection between the definition of \emph{consuming} a
resource in a linear type system and with the fundamental definition of
\emph{evaluation/progress} and the evaluation strategy of a language, making
the \emph{consuming} more precise across languages (in fact, generalizing the
definition of consuming a resource from Linear Haskell).
% \item We present a linear type system that can leverage this connection to be
% more flexible and allow more programs as linearly well-typed.
% \item This type system is defined over a language capturing the linear essence of Core
% \item We prove soundness and that Core optimisations preserve types in this system, where they previously were unable to
\end{itemize}

% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% {{{ Linearity, Semantically
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Linearity, Semantically\label{sec:linearity-semantically}}

A linear type system statically guarantees that linear resources are
\emph{consumed} exactly once. Consequently, whether a program is well-typed
under a linear type system intrinsically depends on the precise definition of
\emph{consuming} a resource. Even though \emph{consuming} a resource is commonly regarded
as synonymous with \emph{using} a resource, i.e. with the syntactic occurrence
of the resource in the program, that is not always the case.
%
In fact, this section highlights the distinction between using resources
syntactically and semantically as a principal limitation of linear type systems
for (especially) non-strict languages, with examples motivated by the
constructs available in GHC Core and how they're evaluated.

% and we show how a linear type system found on
% \emph{consuming resources semantically} rather than \emph{using resources
% syntactically} can accept

Consider the following program in a functional pseudo-language,
where a computation that closes the given |handle| is bound to |x| before the
|handle| is returned:
%
\begin{code}
f : Handle ⊸ Handle
f handle = let x = close handle in handle
\end{code}
%
In this seemingly innocent example, the |handle| appears to be closed before
returned, whereas in fact the handle will only be closed if the let bound
computation is effectively run (i.e. evaluated).
%
The example illustrates that \emph{consuming} a resource is not necessarily
synonymous with using it syntactically, as depending on the evaluation strategy
of the pseudo-language, the computation that closes the handle might or not be
evaluated, and if it isn't, the |handle| in that unused computation
is not consumed.
%
Expanding on this, consider the above example program under distinct
evaluation strategies:
%
\begin{description}

\item[Call-by-value] With \emph{eager} evaluation, the let bound expression |close
handle| is eagerly evaluated, and the |handle| will be closed before being
returned. It is clear that a linear type system should not accept such a
program since the linear resource |handle| is duplicated -- it is used in a
computation that closes it, while still being made available to the caller of
the function.

\item[Call-by-need] On the other hand, with \emph{lazy} evaluation, the let
bound expression will only be evaluated when the binding |x| is needed. We return
the |handle| right away, and the let binding is forgotten as it cannot be
used outside the scope of the function, so the handle is not closed by |f|.
Under the lens of \emph{call-by-need} evaluation, \emph{using} a resource in a
let binding only results in the resource being \emph{consumed} if the binding
itself is \emph{consumed}. We argue that a linear type system under
\emph{call-by-need} evaluation should accept the above program, unlike a linear
type system for the same program evaluated \emph{call-by-value}.

\end{description}
%
%Rather, \emph{consuming} a resource is intrinsically defined by the evaluation model of the language.
%
% Under distinct evaluation strategies, the above example (and programs in general) have different semantics:
%
%
Intuitively, a computation that depends on a linear resource to produce a
result consumes that resource iff the result is effectively computed; in
contrast, a computation that depends on a linear resource, but is never run,
will not consume that resource.

From this observation, and exploring the connection between computation and evaluation,\todo{Alguma dificuldade em dizer exatamente como é que evaluation drives/is computation}
it becomes clear that \emph{linearity} and \emph{consuming resources}, in the
above example and for programs in general, should be defined in function of the
language's evaluation strategy.
%
We turn our focus to \emph{linearity} under \emph{call-by-need}, not only
because GHC Core is \emph{call-by-need}, but also because the distinction between
semantically and syntactically consuming a resource is only exposed under non-strict semantics.
%
Indeed, under \emph{call-by-value}, syntactic occurrences of a linear resource
directly correspond to semantically using that resource\footnote{With the minor exception
of trivial aliases, which don't entail any computation even in
\emph{call-by-value}. In theory, we could use in mutual exclusion any of the
aliases to refer to a resource without loss of linearity} because \emph{all}
expressions are eagerly evaluated -- if all computations are eagerly run, all
linear resources required by computations are \emph{eagerly consumed}.

% ROMES:IMPORTANT:TODO:
% \subsection{Reductions / Function applications}
% 
% \todo[inline]{unrestricted call-by-name with resources can duplicate the resources, as if it were unsound?}
% We reduce function applications in two distinct ways, call by name (for linear
% functions) and call by need (we've now introduced linear lets, so we can look
% at this now)
% 
% Foreshadow to issues with opt (reverse binder swap)?
% 
% Or maybe just drop this section altogether

\subsection{Semantic Linearity by Example\label{sec:semantic-linearity-examples}}

Aligned with our original motivation of typechecking linearity in GHC Core such
that optimising transformations preserve linearity, and with the secondary goal
of understanding linearity in a non-strict context, this section helps the
reader build an intuition for semantic linearity through examples of Core
programs that are semantically linear but rejected by Core's linear type
system.
%
In the examples, a \colorbox{working}{\workingcolorname} background highlights programs that are
syntactically linear and are accepted by Core's naive linear type system. A
\colorbox{notyet}{\notyetcolorname} background marks programs that are
semantically linear, but are not seen as linear by Core's naive linear type
system. Notably, the linear type system we develop in this work accepts all
\colorbox{notyet}{\notyetcolorname} programs.
A \colorbox{noway}{\nowaycolorname} background indicates that the program
simply isn't linear, not even semantically, i.e. the program effectively
discards or duplicates linear resources.

\subsubsection{Let bindings}
We start our discussion with non-strict (non-recursive) let bindings, i.e. let bindings whose
body is evaluated only when the binding is needed, rather than when declared.
In Core, a let binding entails the creation of a \emph{thunk} that suspends the
evaluation of the let body (for background, see
Section~\ref{sec:bg:evaluation-haskell}). When the \emph{thunk} is
\emph{forced}, the evaluation is carried out, and the result overrides the
\emph{thunk} -- the let binding now points to the result of the evaluation. A
\emph{thunk} is \emph{forced} (and the suspended computation is evaluated) when
the binding itself is evaluated.

In a linear type system, a non-strict let binding that depends on a linear
resource |x| doesn't consume the resource as long as the binding isn't
evaluated -- the suspended computation only uses the resource if it is run. For
this reason, we can't naively tell whether |x| is consumed just by looking at
the let binding body. In the following example, we assign a computation that
depends on the resource |x| to a binder, which is then returned:
%
\begin{notyet}
\begin{code}
f1 :: (a ⊸ b) -> a ⊸ b
f1 use x =
  let y = use x
   in y
\end{code}
\end{notyet}
%
The linear resource |x| is used exactly once, since it is used exactly once in
the body of the binding and the binding is used exactly once in the let body.
%
According to Linear Haskell's core calculus ~$\lambda_{\to}^{q}$~\cite{cite:linear-haskell}, let
bound variables are annotated with a multiplicity which is multiplied (as per
the multiplicities semiring) with the multiplicities of the variables that are
free in the binder's body.
%
In short, if a let binder is linear (has
multiplicity $1$) then the linear variables free in its body are only used
once; if the let binder is unrestricted (has multiplicity $\omega$) then the
resources in its body are consumed many times, meaning no linear variables can
occur in that let binder's body.
%
Unfortunately, GHC's implementation of Linear
Haskell doesn't seem to infer multiplicities for lets yet, so while the above
program should typecheck in Linear Haskell, it is rejected by GHC.

The next example exposes the case in which the let binder is ignored in the let
body. Here, the linear resource |x| is used in |y|'s body and in the let
body, however, the resource is still used linearly semantically because |y| isn't used at all, thus |x| is consumed just once in the let body:
%
\begin{notyet}
\begin{code}
f2 :: (a ⊸ a) -> a ⊸ a
f2 use x =
  let y = use x
  in use x
\end{code}
\end{notyet}
%
Programmers don't often write bindings that are completely unused, yet, an
optimising compiler will produce intermediate programs with unused bindings\footnote{Unused bindings are then
also dropped by the optimising compiler} 
from transformations such as inlining, which can substitute out occurrences
of the binder (e.g. |y| is inlined in the let body).

Let bindings can also go unused if they are defined before branching on case
alternatives. At runtime, depending on the branch taken, the let binding will
be evaluated only if it occurs in that branch.
Both optimising transformations (float-out), and programmers used to non-strict evaluation, can produce
programs with bindings that are selectively used in the case alternatives, for
instance:
%
\begin{notyet}
\begin{code}
f3 :: (a ⊸ a) -> Bool -> a ⊸ a
f3 use bool x =
  let y = use x
  in case bool of
      True -> x
      False -> y
\end{code}
\end{notyet}
%
This example essentially merges |f1| with |f2|, using |x| directly in one
branch and using |y| in the other. Semantically, this program is linear because
the linear resource |x| ends up being used exactly once in both case
alternatives, directly or indirectly.

Shifting our focus from not using a let binding to using it (more than once),
we reiterate that a let binding creates a \emph{thunk} which is only evaluated
once, and re-used subsequently. Despite the binder body only being evaluated
once, and thus its resources only used once to compute a result, we can still
only consume said result of the computation once -- perhaps surprisingly, as the
perception so far is that ``resources are consumed during computation'' and
multiple uses of the same let binder share the result that was computed only
once. Illustratively, the following program must \emph{not} typecheck:
%
\begin{noway}
\begin{code}
f4 :: (a ⊸ b) -> a ⊸ (b, b)
f4 use x =
  let y = use x
  in (y, y)
\end{code}
\end{noway}
%
Intuitively, the result of the computation must also be used exactly once,
despite being effectively computed just once, because said result may still
contain (parts of) the linear resource. The trivial example is |f4| applied to
|id| -- the result of computing |id x| is |x|, and |x| must definitely not be
shared! Indeed, if the result of the computation involving the linear resource
was, e.g., an unrestricted integer, then sharing the result would not involve consuming the
resource more than once.
% ROMES:TODO:!!!!
%\todo{this kind of hints that maybe somehow in the
%alternative scrutinizing a "trivial" atom we could make the let binding
%unrestricted after we were sure it was evaluated once, but that isn't easy
%without erasing too many things before, we kind of tried this once}
%
Concretely, the result of evaluating a let binder body using linear resources, if computed, must be
consumed exactly once, or, otherwise, we risk discarding or duplicating said resources.

Lastly, consider a program which defines two let bindings |z| and |y|, where
|z| uses |y| which in turn uses the linear resource |x|:
%
\begin{noway}
\begin{code}
f5 :: (a ⊸ a) -> a ⊸ ()
f5 use x =
  let y = use x
  let z = use y
  in ()
\end{code}
\end{noway}
%
Even though the binding |y| is used in |z|, |x| is still never consumed because
|z| isn't evaluated in the let body, and consequently |y| isn't evaluated
either -- never consuming |x|. We use this example to highlight that even for
let bound variables, the syntactic occurrence of a variable isn't enough to
determine whether it is used. Instead, we ought to think of uses of |y| as
implying using |x|, and therefore uses of |z| imply using |x|, however, if
neither is used, then |x| isn't used. Since |x| is effectively discarded, this
example also violates linearity.

\parawith{Summary}
The examples so far build an intuition for semantic linearity in the presence
of lazy let bindings. In essence, an unused let binding doesn't consume any
resources, and a let binding used exactly once consumes its resources exactly
once. Let binders that depend on linear resources must be used \emph{at most
once} -- let bound variables are \emph{affine} in the let body.
%
Moreover, if the let binding ($y$) isn't used in the let body, then the
resources it depends on ($\ov{x}$) must still be used -- the binding $y$ is
mutually exclusive with the resources $\ov{x}$ (for the resources to be used
linearly, either the binder occurs exactly once $y$, or the resources $\ov{x}$
do). We'll later see how we can encode this principle of mutual exclusivity
between let bindings and their dependencies using so called \emph{usage
environments}, in Section~\ref{sec:usage-environments}.

\subsubsection{Recursive let bindings}
Second, we look into recursive let bindings. For the most part,
recursive let bindings behave as non-recursive let bindings, i.e. we must use them \emph{at
most once} because, when evaluated, the linear resources used in the binders
bodies are consumed. The defining property of a group of mutually recursive let
bindings is that the binders bound in that group can occur, without restrictions, in
the bodies of those same binders. The same way that, in a let body, evaluating
a binding that uses some resource exactly once consumes that resource once,
using the binding in its own definition also entails using that resource once.
Consider the following program, that calls a recursive let-bound function
defined in terms of the linear resource |x| and itself:
%
\begin{notyet}
\begin{code}
f6 :: Bool -> a ⊸ a
f6 bool x =
  let go b
        = case b of
           True -> x
           False -> go (not b)
  in go bool
\end{code}
\end{notyet}
%
Function |f6| is semantically linear because, iff it is consumed exactly once,
then |x| is consumed exactly once. We can see this by case analysis on |go|'s argument
\begin{itemize}
\item When |bool| is |True|, we'll use the resource |x|
\item When |bool| is |False|, we recurse by calling |go| on |True|, which in turn will use the resource |x|.
\end{itemize}
In |go|'s body, |x| is used directly in one branch and indirectly in the
other, by recursively calling |go| (which we know will result in using |x|
linearly).
% ROMES:TODO:!!
%\todo{this bit is quite hard to explain. It is some sort of cyclic
%argument -- we kind of assume go uses x linearly s.t. when go itself is used
%then we're using x linearly. recursion...}
%
It so happens that |go| will terminate on any input, and will always consume
|x|. However, termination is not a requirement for a binding to use |x| linearly,
and we could have a similar example in which |go| might never terminate but still
uses |x| linearly if evaluated:
%
\begin{notyet}
\begin{code}
f7 :: Bool -> a ⊸ a
f7 bool x =
  let go b
        = case b of
           True -> x
           False -> go b
  in go bool
\end{code}
\end{notyet}
%
The key to linearity in the presence of non-termination is Linear Haskell's
definition of a linear function: \emph{if a linear function application (|f u|) is
consumed exactly once, then the argument (|u|) is consumed exactly once}.
If |f u| doesn't terminate, it is never consumed, thus the claim holds
vacuously; that's why |f8| typechecks:
\begin{working}
\begin{code}
f8 :: a ⊸ b
f8 x = f8 x
\end{code}
\end{working}
%
If |go| doesn't terminate, we aren't able to compute (nor consume) the result
of |f7|, so we do not promise anything about |x| being consumed (|f7|'s
linearity holds trivially). If it did terminate, it would consume |x| exactly
once (e.g. if |go| was applied to |True|).

Determining the linear resources used in a recursive binding might feel
peculiar since we need to know the linear resources used by the binder to determine the linear resources it uses.
%
The paradoxical definition is difficult to grasp, just how learning that a
function can be defined in terms of itself is perplexing when one is first
introduced to general recursion.
%
Informally, we \emph{assume} the binding will consume some linear resources
exactly once, and use that assumption when reasoning about recursive calls such
that those linear resources are used exactly once.

%This high-level reasoning isn't amenable for a computer that must check
%whether the program is linear.

Generalizing, we need to find a set of linear resources ($\Delta$) that satisfies the recursive equation
\footnote{This set of resources will basically be the least upper bound of the sets of resources used in each
mutually recursive binding scaled by the times each binding was used}
arising from given binding $x$, such that:
\begin{enumerate}
\item Occurrences of $x$ in its own body are synonymous with using all resources in $\Delta$ exactly once,
\item And if the binding $x$ is fully evaluated, then all resources in $\Delta$ are consumed exactly once
\end{enumerate}
Finding a solution to this equation is akin to finding a (principle) type for a
recursive binding: the binding needs to be given a type such that occurrences of
that binding in its own body typecheck using that type.
%
Foreshadowing, the core system we developed assumes recursive let bindings to
be annotated with a set of resources satisfying the equations; but we also
present an algorithm to determine this solution, and distinguish between an
\emph{inference} and a \emph{checking} phase, where we first determine the
linear resources used by a group of recursive bindings and only then check
whether the binding is linear, in our implementation of checking of recursive
lets.
% ROMES:TODO:!!!
%\todo{We might not need the inferrence phase, somehow. Anyhow it seems like
%our inferrence is not really about determining a solution but more about
%determining how many times each thing gets used}

There might not be a solution to the set of equations. In this case, the
binding undoubtedly entails using a linear resource more than once. For
example, if we use a linear resource |x| in one case alternative, and invoke
the recursive call more than once, we might eventually consume |x| more than
once:
%
\begin{noway}
\begin{code}
f9 :: Bool -> Bool ⊸ Bool
f9 bool x =
  let go b
        = case b of
           True -> x
           False -> go (not b) && go True
  in go bool
\end{code}
\end{noway}
Note that if returned |x| instead of |go bool| in the let body, then, despite
the binding using |x| more than once, we would still consume |x| exactly once,
since recursive bindings are still lazy.

Lastly, we extend our single-binding running example to use two mutually recursive bindings that
depend a linear resource:
\begin{notyet}
\begin{code}
f10 :: Bool -> a ⊸ a
f10 bool x =
  let go1 b
        = case b of
           True -> go2 b
           False -> go1 (not b)
      go2 b
        = case b of
           True -> x
           False -> go1 b
  in go1 bool
\end{code}
\end{notyet}
As before, we must find a solution to the set of equations defined by the
mutually recursive bindings to determine which resources will be consumed.
In this case, |go1| and |go2| both consume |x| exactly once if evaluated.
We additionally note that a strongly connected group of recursive bindings
(i.e. all bindings are transitively reachable from any of them) will always
consume the same set of resources -- if all bindings are potentially reachable,
then all linear resources are too.

\parawith{Summary}
Recursive let bindings behave like non-recursive let bindings in that if they
aren't consumed, the resources they depend on aren't consumed either.  However,
recursive let bindings are defined in terms of themselves, so the set of linear
resources that will be consumed when the binder is evaluated is also defined in
terms of itself (we need it to determine what resources are used when we
recurse). We can intuitively think of this set of linear resources that will be
consumed as a solution to a set of equations defined by a group of mutually
recursive bindings, which we are able to reason about without an algorithm for
simpler programs. In our work, the core type system isn't concerned with
deriving said solution, but we present a simple algorithm for inferring with
our implementation.

\subsubsection{Case expressions}

Finally, we discuss semantic linearity for case expressions, which have been
purposefully left for last as the key ingredient that brings together the
semantic linearity insights developed thus far, because, essentially,
\emph{case expressions drive evaluation} and semantic linearity can only be
understood in function of how expressions are evaluated.

Up until now, the example functions have always linearly transformed linear
resources, taking into consideration how expressions will be evaluated (and thus
consumed) to determine if resources are being used linearly. However, there
have been no examples in which linear resources are \emph{fully consumed} in
the bodies of linear functions. In other words, all example functions so far
return a value that has to be itself consumed exactly once to ensure the linear
argument is, in turn, consumed exactly once -- as opposed to functions whose
application simply needs to be evaluated to guarantee its linear argument is
consumed (functions that return an unrestricted value).
%
%The latter are of particular relevance because linearly-typed abstractions
%usually require such a function to provide newly-created linear resources to.
%
For example, the entry point to the linear array API presented in Linear
Haskell takes such a function as its second argument:
\begin{working}
\begin{code}
newMArray :: Int -> (MArray a ⊸ Unrestricted b) ⊸ b
\end{code}
\end{working}
%(The second argument is a function that consumes |MArray a| linearly
%and returns an unrestricted result -- we don't need to consume said result
%exactly once to guarantee that |MArray a| is used linearly in the function
%body.)

% ROMES:TODO: Há qualquer coisa que não gosto nada! na coerência deste paragrafo

In short, case expressions enable us to consume resources and thus write
functions that fully consume their linear arguments. To understand exactly how,
we turn to the definition of \emph{consuming} a resource from Linear
Haskell~\cite{cite:linearhaskell}:
\begin{itemize}
    \item To consume a value of atomic base type (such as~\texttt{Int} or
        \texttt{Ptr}) exactly once, just evaluate~it.
    \item To consume a function value exactly once, apply it to one argument,
        and consume its result exactly once.
    \item To consume a value of an algebraic datatype exactly once,
        pattern-match on it, and consume all its linear components exactly once.
        % For example, a linear pair (equivalent to $\tensor$) is consumed exactly
        % once if pattern-matched on \emph{and} both the first and second element are
        % consumed once.
\end{itemize}
That is, we can consume a linear resource by fully evaluating it, through case
expressions. In section \ref{sec:generalizing-evaluation-consuming} we
generalize the idea that consuming a resource is deeply tied to evaluation.
Here, we continue building intuition for semantic linearity, first reviewing
how case expressions evaluate expressions, and then exploring how they consume
resources, by way of example.

In Core, case expressions are of the form $\ccase{e_s}{z~\{\ov{\rho_i \to e_i}\}}$,
where $e_s$ is the case \emph{scrutinee}, $z$ is the case \emph{binder}, and
$\ov{\rho_i \to e_i}$ are the case \emph{alternatives}, composed of a pattern
$\rho_i$ and of the corresponding expression $e_i$. Critically:
\begin{enumerate}
\item The case scrutinee is always evaluated to Weak Head Normal Form (WHNF).

\item Evaluating to WHNF an expression that is already in WHNF is a no-op, that is,
no computation whatsoever occurs, unlike evaluating a e.g. function application.

\item The case binder is an alias to the result of evaluating the scrutinee to WHNF.

\item The alternative patterns are always exhaustive, i.e. there always exists
a pattern that matches the WHNF of a value resulting from evaluating the
scrutinee, where a pattern is either a wildcard that matches all expressions
($\_$), or a constructor and its linear and non-linear component binders
($K~\ov{x}\ov{y}$, with $\ov{x}$ as linearly-bound variables and $\ov{y}$ as
unrestricted ones).

\end{enumerate}

% ROMES:TODO: We should talk about WHNF in the background, not here.
% \parawith{WHNF} An expression is in Weak Head Normal Form when 

To explore these case properties in the presence of linearity, we start with an
example of a program that constructs a tuple from linear resources then pattern
matches on it, then uses both linearly-bound variables from the tuple pattern
match. This is well-typed in Linear Haskell:
\begin{working}
\begin{code}
f11 :: a ⊸ b ⊸ (a ⊸ b ⊸ c) -> c
f11 x y use = case (x,y) of { (a,b) -> use a b }
\end{code}
\end{working}
What might be more surprising is that a similar program which discards the
pattern variables and instead uses the resources in the scrutinee is also
semantically linear, despite not being accepted by Linear Haskell:
\begin{notyet}
\begin{code}
f12 :: a ⊸ b ⊸ (a ⊸ b ⊸ c) -> c
f12 x y use = case (x,y) of z { (a,b) -> use x y }
\end{code}
\end{notyet}
We justify that |f12| is linear by appealing to property 2 -- since the
expression (the tuple) being scrutinized is already in WHNF, evaluating it will
not consume neither $x$ nor $y$. Even if the tuple was constructed with
two expressions using $x$ and $y$ respectively, no computation would happen
since we aren't using neither $a$ nor $b$ (thereby never forcing the arguments
of the tuple). However, if we did use $a$ in the case body, then $x$ would be unavailable:
\begin{noway}
\begin{code}
f13 :: a ⊸ a ⊸ (a ⊸ a ⊸ c) -> c
f13 x y use = case (x,y) of z { (a,b) -> use a x }
\end{code}
\end{noway}
This idea that $x$ and $a$ are mutually exclusive is the same behind let
bindings being mutually exclusive to the resources that define them.
By forcing the pattern variable (or the let binding) we run the computations
defined in terms of the linear variables used for that constructor argument (or
let binder body), but otherwise, if we don't use those binders, then we don't
run the computation thus no resources are consumed.

A third option for this example is to use the case binder $z$ instead of $a,b$ or $x,y$:
\begin{notyet}
\begin{code}
f14 :: a ⊸ b ⊸ (a ⊸ b ⊸ c) -> c
f14 x y use = case (x,y) of z { (a,b) -> uncurry use z }
\end{code}
\end{notyet}
Again, $z$ is mutually exclusive with $a,b$ and with $x,y$, but at least one of
the three must occur to ensure the linear resources are consumed. In this
example, we can think that using $a$ entails using the resource $x$, $b$ the
resource $y$, and the case binder $z$ entails using both $a$ and $b$.

Dually, consider the scrutinee to be an expression that's not in WHNF, s.t.
evaluating it to WHNF will require doing computation and thus consume linear
resources that are used in it:
\begin{notyet}
\begin{code}
f15 :: a ⊸ b ⊸ (a ⊸ b ⊸ (c,d)) -> (c,d)
f15 x y use = case use x y of z { (a,b) -> z }
\end{code}
\end{notyet}
Unlike when the scrutinee was in WHNF, we can no longer use $x,y$ in the case
alternatives, but we \emph{must} still use either the case binder $z$ or the linear
pattern variables $a,b$, e.g. it would be quite disastrous if any of the following typechecked:
\begin{noway}
\begin{code}
doubleFree :: Ptr ⊸ (Ptr ⊸ Result) -> Result
doubleFree x free = case free x of z { Result v -> free x }
\end{code}
\end{noway}
\begin{noway}
\begin{code}
leakPointer :: Ptr -> ()
leakPointer x = case id x of z { _ -> () }
\end{code}
\end{noway}
%
%whereas this is fine:
%\begin{notyet}
%\begin{code}
%f16 :: Ptr ⊸ (Ptr ⊸ (Value,Int)) -> (Value,Int)
%f16 x free = case K (free x) of z { K y -> free x }
%\end{code}
%\end{notyet}
%
The result of evaluating the scrutinee must be consumed exactly to guarantee
that the resources used in the scrutinee are fully consumed, or risk them being only ``almost'' consumed. Take for example
|use| in |f15| to simply be |(,)|: it is not sufficient for |use x y| to be
evaluated to WHNF to consume |x| and |y|. Otherwise, if all the resources were
considered to be fully consumed after the scrutinee were evaluated in a case
expression, we could simply ignore the pattern variables, effectively
discarding linear resources (for cases such as the |use = (,)| example). In
short, if the scrutinee is not in WHNF we must either consume the case binder
or the linear components of the pattern.

However, it is crucial to also consider pattern matches on constructors without
any linear components. If the constructor has no linear fields, it means the
result can be consumed unrestrictedly and, therefore, all linear resources used
in the computation have been fully consumed. For instance, the following
program, where |K2| has no fields and |K1| has one linear field, shouldn't
typecheck because in case alternatives that matched a constructor without
linear fields the scrutinee resources are no longer available:
\begin{noway}
\begin{code}
f :: a ⊸ a
f x = case K1 x of z { K2 -> x; K1 a -> x }
\end{code}
\end{noway}
\todo[inline]{Actually, this example is fine; in practice, it only matters that
resources are consumed to be able to use the case binder unrestrictedly. This
one doesn't typecheck, but is still semantically linear}
This particular example has a known constructor being scrutinized which might
seem like an unrealistic example, but we recall that during the transformations
programs undergo in an optimizing compiler, many programs such as this
naturally occur (e.g. if the definition of a function were inlined in the scrutinee).

Moreover, in a branch of a constructor without linear fields we also know the
result of evaluating the scrutinee to be unrestricted, so we can also use the
case binder unrestrictedly and refer to it zero or more times. For example, this
program is also linear:
\begin{notyet}
\begin{code}
f16 :: () ⊸ ()
f16 x = case x of z { () -> z <> z }
\end{code}
\end{notyet}

Further exploring that each linear field must be consumed exactly once, and
that resources in WHNF scrutinees aren't consumed, we are able to construct
more contrived examples, the following two of which the first doesn't typecheck
because the same linear field is used twice, but the second one does since it
uses each linear field exactly once (despite pattern matching on the same
components twice)
\begin{noway}
\begin{code}
f w = case w of z
        (a,b) ->
          case (a,b) of z'
            (c,d) ->
               (a,c)
\end{code}
\end{noway}
\begin{notyet}
\begin{code}
f w = case w of z
        (a,b) ->
          case (a,b) of z'
            (c,d) ->
               (a,d)
\end{code}
\end{notyet}

Finally, we consider the default case alternatives, also known as wildcards
(written $\_$), in the presence of linearity: Matching against the wildcard
doesn't provide new information, so we linearity is seen as before but without
fully consuming linear resources (in non-linear patterns) nor binding new
linear resources (in linear patterns). If the scrutinee is in WHNF, we can
either use the resources from the scrutinee or the case binder in that
alternative, if the scrutinee is not in WHNF, we \emph{must} use the case
binder, as it's the only way to linearly consume the result of evaluating the
scrutinee to WHNF.

\parawith{Summary} Case expressions evaluate their scrutinees to WHNF,
introduce a case binder, and bind pattern variables. If the scrutinee is
already in WHNF, all resources occurring in it are still available in the case
alternative, alongside the case binder and the pattern-bound variables. In the
case alternative, either the resources of the scrutinee, the case binder, or
the linearly bound pattern variables must be used exactly once, but mutually
exclusively. For scrutinees not in WHNF, in the case alternative, either the
case binder or the linear pattern variables must be used mutually exclusively.
If the pattern doesn't bind any linear resources, then it may be consumed
unrestrictedly, and therefore the case binder may also be used unrestrictedly.

% This is fine, because |x| in the case alternative is known to be K...
% Variables really are weird case...
% ROMES:TODO: Do something about this?
% \begin{noway}
% \begin{code}
% f :: a ⊸ (a ⊸ K) ⊸ a
% f x use = case x of z { K -> x }
% \end{code}
% \end{noway}

%We used to call NOT IN WHNF "negative" hah
%\begin{code}
%-- This is NOT OK since (g x y) is negative (eliminates g)
%f x y = case g x y of z
%          K1 a b -> (x,y)
%          K2 w   -> (x,y)
%\end{code}


%% The harder harder things

%\todo[inline]{Should we discuss this? It would be fine, but we're not able to see this because of call-by-name substitution}
%\begin{code}
%f x = case x of z { _ -> x }
%\end{code}

%\todo[inline]{the harder ones regarding reverse binder swap. these give some
%intuition, but this is an unsound optimisation in some contexts}
%\begin{code}
%f y = let x = use y
%       in case x of z { K a b -> expensive x; K2 w -> w }
%\end{code}
%
%\begin{code}
%f y = let x = use y
%      let t = expensive x
%       in case x of z { K a b -> t; K2 w -> w }
%\end{code}
%
%\begin{code}
%f x = case x of z { K a b -> expensive x; K2 w -> w }
%
%
%f y = let x = use y
%       in case x of z { K a b -> expensive x; K2 w -> w }
%
%
%f y = let x = use y
%      let t = expensive x
%       in case x of z { K a b -> t; K2 w -> w }
%\end{code}

\subsection{Generalizing linearity in function of evaluation\label{sec:generalizing-evaluation-consuming}}

Indeed, as hinted towards in the previous section, there's a deep connection
between \emph{evaluation} and \emph{consuming resources}.

Definition X.Y: A linear resource is consumed when it is either fully evaluated
(NF) to a value, or when it is returned s.t. an application of that function
being fully evaluated would fully evaluate the resource to a value. Or something like that.
%
Note how this generalizes Linear Haskell's definition of consuming a resource: $\dots$

\begin{itemize}
\item We could almost say that eventually everything all linear
resources must be evaluated to NF to be consumed, or returned by a function
s.t. a continuation of that function has to evaluate the result to NF., or something.

\item Discuss our own generalized (call-by-value, call-by-name, etc)
definition of consuming resources by evaluation. Something like, if an
expression is fully evaluated, all linear resources that expression depends on
to compute a result are consumed, or something...

\item How does this relate to strictness? Reference the section of Linear
Haskell about linearity and strictness, and basically revisit what they say.

\end{itemize}
  

% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% {{{ Linear Core
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Linear Core}

In this section, we develop a linear calculus $\lambda_\Delta^\pi$, dubbed \emph{Linear Core}, that 
combines the linearity-in-the-arrow and multiplicity polymorphism introduced by
Linear Haskell~\cite{linearhaskell} with all the key features from GHC's Core
language, except for type equality coercions\footnote{We explain a main avenue of
future work, multiplicity coercions, in Section~\ref{sec:future-work}}.
%
Specifically, our core calculus is a linear lambda calculus with
algebraic datatypes, case expressions, recursive let bindings, and multiplicity
polymorphism.

Linear Core makes much more precise the various insights discussed in the
previous section by crystallizing them together in a linear type system for which we
prove soundness via the usual preservation and progress theorems. Crucially,
the Linear Core type system accepts all the \emph{semantically linear} example
programs (highlighted with \colorbox{notyet}{\notyetcolorname})
from Section~\ref{sec:semantic-linearity-examples}, which Core currently
rejects.
%
Besides type safety, we prove that multiple optimizing Core-to-Core
transformations preserve linearity in Linear Core. These same transformations
don't preserve linearity under Core's current type system. As far as we know,
we are the first to prove optimisations preserve types in a non-strict linear
language?

The first key idea for typing linearity semantically is to delay \emph{consuming a
resource} to when a computation that depends on that resource is effectively
evaluated or returned, by annotating relevant binders with \emph{usage
environments} (\S~\ref{sec:usage-environments}).
%
The second key idea is to have two distinct rules for
case expressions, branching on whether the scrutinee is in Weak Head Normal
Form, and using ``proof irrelevance'' to track resources that are no
longer available but haven't yet been fully consumed (\S~\ref{sec:lc-case-exps}). Additionally, we introduce
tagged resources to split the resources between the pattern-bound variables as
usage environments, encoding that pattern variables jointly ``finish
consuming'' the scrutinee resources.
% 
We also note that despite the focus on GHC Core, the fundamental ideas for
understanding linearity in a call-by-need calculus can be readily applied to
other call-by-need languages.

We present Linear Core's syntax and type system iteratively, starting with the
judgements and base linear calculi rules for multiplicity and term lambdas plus
the variable rules ($\S~\ref{sec:base-calculi}$).
%
Then usage environments, the rule for $\Delta$-bound variables, and rules for
(recursive) let bindings ($\S~\ref{sec:usage-environments}$).
%
Finally, we introduce the rules to typecheck case expressions and alternatives,
along with the key insights to do so, namely branching on WHNF-ness of
scrutinee, proof irrelevant resources, and tagged variables
($\S~\ref{sec:lc-case-exps}$).

% We start by introducing the Core-like language, $\dots$ usage environments as a
% way to encode choice between the way a resource is used $\dots$\todo{$\dots$}
%

%\todo[inline]{Explicar algumas das ideias fundamentais, e apresentar as regras
%iterativamente. Podemos começar com as triviais e avançar para os dois pontos
%mais difíceis : Lets e Cases}

\subsection{Language Syntax}

The complete syntax of Linear Core is given by Figure~\ref{fig:full-linear-core-syntax}.
% Figure~\ref{fig:linear-core-types} and Figure~\ref{fig:linear-core-terms}.
%
The types of Linear Core are algebraic datatypes, function types, and multiplicity schemes
to support multiplicity polymorphism: datatypes ($T~\ov{p}$) are parametrised
by multiplicities, function types ($\vp\to_\pi\s$) are also annotated with a
multiplicity, and a multiplicity can be $1$, $\omega$ (read \emph{many}), or a
multiplicity variable $p$ introduced by a multiplicity universal scheme
($\forall p.~\vp$).
%
\[
\SyntaxTypes
\]
%
The terms are variables $x,y,z$, data constructors $K$, multiplicity
abstractions $\Lambda p.~e$ and applications $e~\pi$, term abstractions
$\lambda \x[\pi].~e$ and applications $e~e'$, where lambda binders are
annotated with a multiplicity $\pi$ and a type $\s$. Then, there are
non-recursive let bindings $\llet{\xD = e}{e'}$, recursive let bindings
$\lletrec{\ov{\xD = e}}{e'}$, where the overline denotes a set of distinct
bindings $x_1{:}_{\D_1}\s_1\dots x_n{:}_{\D_n}\s_n$ and associated expressions
$e_1\dots e_n$, and case expressions $\ccase{e}{\zD~\{\ov{\rho \to e'}\}}$,
where $z$ is the case binder and the overline denotes a set of distinct
patterns $\rho_1\dots \rho_n$ and corresponding right hand sides $e'_1\dots
e'_n$. Notably, (recursive) let-bound
binders and case-bound binders are annotated
with a so-called \emph{usage environment} $\Delta$ -- a fundamental construct
for type-checking semantic linearity in the presence of laziness we present in
Section~\ref{sec:usage-environments}.
%
Case patterns $\rho$ can be either the \emph{default} or \emph{wildcard}
pattern $\_$, which matches any expression, or a constructor $K$ and a set of
variables that bind its arguments, where each field of the constructor has an
associated multiplicity denoting whether the pattern-bound variables must
consumed linearly (ultimately, in order to consume the scrutinee linearly).
Additionally, the set of patterns in a case expression is guaranteed to be exhaustive,
i.e. there is always at least one pattern which matches the scrutinized expression.
\[
\SyntaxTerms
\]
Linear Core takes the idea of annotating lets with usage environments from the
unpublished Linear Mini-Core document by Arnaud Spiwack et.
all~\cite{cite:linear-mini-core}, which first tentatively tackled Core's
linearity issues. We discuss this work in more detail in
Section~\ref{sec:linear-mini-core}.

Datatype declarations $\datatype{T~\overline{p}}{\overline{K:\overline{\sigma
\to_\pi}~T~\overline{p} }}$ involve the name of the type being declared $T$
parametrized over multiplicity variables $\ov{p}$, and a set of the data
constructors $K$ with signatures indicating the type and multiplicity of the
constructor arguments. Note that a linear resource is used many times when a
constructor with an unrestricted field is applied to it, since, dually, pattern
matching on the same constructor with an unrestricted field allows it to be
used unrestrictedly. Programs are a set of declarations and a top-level
expression.

\SyntaxFull

%Linear Core is similar to Core without coercions, and with multiplicity
%abstractions instead of type abstractions.
%The key differences are that lets, recursive lets, case binders and
%pattern-bound variables
%the product of combining Linear Haskell's arrow linearity and
%multiplicity polymorphism with Core's key features, except for type equality
%coercions --
%a linear lambda calculus with algebraic datatypes, case
%expressions, recursive let bindings, and multiplicity abstractions. The 

\subsection{Typing Foundations\label{sec:base-calculi}}

Linear Core ($\lambda^\pi_\Delta$) is a linear lambda calculus akin to Linear Haskell's
$\lambda^q_\to$ in that both have multiplicity polymorphism, (recursive) let
bindings, case expressions and algebraic data types. $\lambda^\pi_\Delta$
diverges from $\lambda^q_\to$ primarily when typing lets and case expressions
and alternatives, in its purpose to typecheck semantic linearity.
%, and secondarily in only treating multiplicity polymorphism superficially.
%
\todo{And our treatment of multiplicity
polymorphism completely ignores algebraic treatment of multiplicities with
semiring operations!!! Would it be sufficient to add a rule for application of variable multiplicity functions?}
%
Otherwise, the base rules of the calculus for, multiplicity and term,
abstraction and application are quite similar. In this section we present the
linear calculi with rules that share much in common with $\lambda^p_\to$, and
in the subsequent ones the rules encoding the novel insights from Linear Core
explored by example in Section~\ref{sec:linearity-semantically}.

We start with the main typing judgement. As is customary for linear type
systems, we use two typing environments, an \emph{unrestricted} $\G$ and
a \emph{linear} $\D$ environment.
%
Variables in $\G$ can be freely discarded (\emph{weakened}) and duplicated
(\emph{contracted}), while resources in $\D$ must be used exactly once (hence
can't be discarded nor duplicated). Despite not having explicit weakening and
contraction rules in our system, they are available as admissible rules for
$\G$ (but not for $\D$), since, equivalently (via
\cite{91621fae-5e53-3497-8291-32b2fab5a743}), resources from $\G$ are
duplicated for sub-derivations and may unrestrictedly exist in the variable
rules.
% TODO: Likely rewrite that
%
The judgement reads ``expression $e$ has type
$\s \to \vp$ under the unrestricted environment $\G$ and linear environment $\D$'':
\[
\G;\D \vdash e : \s \to \vp
\]
Occurrences of unrestricted variables from $\G$ are well-typed if the linear
environment is empty, while occurrences of linear variables are only well-typed
when they're the only resource available in the linear context.
\[
\begin{array}{cc}
\TypeVarOmega & \TypeLinearVar
\end{array}
\]
In both cases, the linear context must contain exactly what is required to
prove the terminal case, whereas the unrestricted context may contain arbitrary
variables.
%
Variables in contexts are annotated with their type and multiplicity, so
$\x[\pi]$ is a variable named $x$ of type $\s$ and multiplicity $\pi$.

Linear functions are introduced via the function type ($\s \to_\pi \vp$) with
$\pi = 1$, i.e. a function of type $\s \to_1 \vp$ (or $\s \lolli \vp$)
introduces a linear resource in the linear environment $\D$.
%
Unrestricted functions are introduced via the same function type with $\pi =
\omega$, and the $\lambda$-bound variable is added to $\G$:
\[
\begin{array}{cc}
\TypeLamIntroL & \TypeLamIntroW
\end{array}
\]
A linear function application is well-typed if there exists a disjoint split of the
linear resources into $\D,\D'$ set. the function and argument, each under a
distinct split, are both well-typed and the argument type matches the
function's expected argument type. Conversely, unrestricted resources are
duplicated and available whole to both sub-derivations.
\[
\TypeLamElimL
\]
An unrestricted function, unlike a linear one, consumes its argument
unrestrictedly (zero or more times). Therefore, in an unrestricted function
application, allowing any linear resources to occur in the argument expression
would entail possibly consuming those resources not linearly, since the
variable binding the argument expression could be discarded or used more than
once in the function body. Thus, arguments to unrestricted functions must also
be unrestricted, i.e. no linear variables can be used to type them.
\[
\TypeLamElimW
\]
Typing linear and unrestricted function applications separately is less general
than a typing rule for any multiplicity $\pi$ that scales per the multiplicity
ring the resources used by the argument, however, since our goal of semantic
linearity not benefiting much from it, keeping the simple approach allows us to have
the linear and unrestricted environments separate.\todo{We might only need multiplicities for the
case-of-case definition as it exists in ghc?, even then couldn't we do semiring scaling without variables? Also, dislike sentence}

Multiplicity abstractions ($\Lambda p.~e$) introduce a multiplicity variable
$p$ to the unrestricted context as well, since we don't impose usage
restrictions on multiplicity variables, and introduce expressions of type
$\forall p.~\dots$, i.e. terms universally quantified over a multiplicity
variable. We note that, in the body of the abstraction, function types annotated
with a $p$ variable and data type fields with multiplicity $p$ are equivalent
to linear functions and linear fields -- if $p$ can be instantiated at both
$\omega$ and $1$, it must be well-typed for both instantiations, which is only
true if multiplicity-polymorphic functions and fields are treated as linear
functions and fields.
\[
\TypeMultLamIntro
\]
A multiplicity application instantiates a multiplicity-polymorphic type
$\forall p.~\s$ at a particular (argument) multiplicity $\pi$, resulting in an
expression of type $\s$ where occurrences of $p$ are substituted by $\pi$, i.e.
$\s[\pi/p]$.
\[
\TypeMultLamElim
\]
The rule additionally requires that $\pi$ must be \emph{well-formed} in order
for the expression to be well-typed, using the judgement $\G \vdash_{mult}
\pi$, where well-formedness is given by $\pi$ either being $1$, $\omega$, or an
in-scope  multiplicity variable in $\G$.
\[
\TypeWellFormedMult
\]

These rules conclude the foundations of our linear calculi. In subsequent
sections we type-check (recursive) let bindings and case expressions,
accounting for semantic linearity as per the insights construed in
Section~\ref{sec:linearity-semantically}, effectively distilling them into the
key ideas of our work, encoded as rules.

\subsection{Usage environments\label{sec:usage-environments}}

A \emph{usage environment} $\Delta$ is the means to encode the powerful idea
that lazy bindings don't consume the resources required by the bound expression
when defined, but rather when themselves are fully consumed. Specifically, we
annotate so-called $\Delta$-bound variables with a \emph{usage environment} to
denote that consuming these variables equates to consuming the resources in the
usage environment they are annotated with, where a usage environment is
essentially a multiset of linear resources. $\Delta$-bound variables are
introduced by a handful of constructs, namely (recursive) let binders, case
binders, and case pattern variables. For example, as per the insights into
semantic linearity developed in Section~\ref{sec:semantic-linearity-examples},
only were we to evaluate and consume $u$ in $e$ would we use the resources
consumed in its body, $x$ and $y$, in the following program. Accordingly, the
usage environment of $u$ would be $\{x,y\}$:
\[
f = \lambda \xl.~\lambda \y[1].~\llet{u = (x,y)}{e}
\]
Furthermore, usage environments guarantee that using a $\Delta$-bound variable
is mutually exclusive with directly using the resources it is annotated with.
In practice, using the $\Delta$-bound variable consumes all linear resources
listed in its usage environment, meaning they are no longer available for
direct usage. Dually, using the linear resources directly means they are no
longer available to consume through the usage environment of the $\Delta$-bound
variable.

Finally, we note how usage environments bear a strong resemblance to the linear
typing environments to the right of the semicolon in the main typing judgement,
i.e. the environment with the linear resources required to type an expression.
%
In fact, usage environments and linear typing contexts differ only in that the
former are used to annotate variables, while the latter used to type
expressions. Yet, this distinction is slightly blurred when introducing how
typing environments are moved to usage environments, or otherwise used in rules
relating the two.

\subsubsection{Delta-bound variables}

A $\Delta$-bound variable $u$ is a variable annotated with a usage environment $\Delta$. Crucially, for any $\Delta$-bound variable $u$,
%
\begin{enumerate}
\item Using $u$ is equivalent to using all the linear resources in $\Delta$
\item $u$ can only be used once
\item Using $u$ is mutually exclusive with using the $\Delta$ resources it depends on elsehow
\item $u$ can be safely discarded as long as the resources in $\Delta$ are consumed elsehow
\end{enumerate}
%
Fortunately, since linear resources must be linearly split across
sub-derivations, (2) and (3) follow from (1), since consuming the linear resources
in $\Delta$ to type $u$ makes them unavailable in the context of any other
derivation. Therefore, also using them directly, or indirectly through the same
(or other) usage environment, is impossible to type-check as the resources were
already allocated to the derivation of $u$. Similarly, (4) also follows from
(1), because if the linear resources aren't consumed in the $\Delta$-var
derivation, they must be consumed in an alternative derivation (or otherwise
the expression does not typecheck).

These observations all boil down to one typing rule for $\Delta$-bound
variables, which fundamentally encodes (1), implying the other three bullets:
\[
\TypeVarDelta
\]
The rule reads that an occurrence of a $\Delta$-bound variable is well-typed if
the linear environment is exactly the resources in the usage environment of
that variable.

$\D$-variables are always introduced in $\Gamma$ since they can be discarded and
duplicated, despite multiple occurrences of the same $\Delta$-variable not possibly
being well-typed since, ultimately, those occurrences imply usage of resources
that must be used linearly.


\subsubsection{Lazy let bindings}

In Section~\ref{sec:semantic-linearity-examples}, we discussed how,
semantically, lazy let bindings consume the resources used in their bodies
lazily, just how the expressions are also evaluated lazily.
%
Resources in let-bound expressions are only consumed when the binder of that
expression is fully consumed and must occur in mutual exclusion with the
resources used in that expression.
%
Indeed, this is exactly what usage environments encode -- let-bound variables
are the canonical example of a $\Delta$-bound variable, a variable bound to an
expression in which the resources required to type it are consumed lazily (when
evaluated) rather than eagerly, effectively \emph{delaying} the consumption of
resources to when they're really needed.

Summarily, let-bindings introduce $\Delta$-variables whose usage environment
are the linear typing environments of the bindings' bodies.
\[
\TypeLet
\]

\todo[inline]{Let bindings are hard, if they are used then we use resources. If
they don't get used then we use no resources! In practice, resources that show
up in the body of the let must be used, be it by using the let binder, or by
using them directly. This makes the let binder and the resources in its body
mutual exclusive.}

\todo[inline]{Explain the idea of suspended computation, and how resources will
be consumed to some extent when we force the computation -- also foreshadowing
that evaluation to WHNF doesn't necessarily consume all resources}

\todo[inline]{Assign usage environments to let-bound variables, trivial usage
of usage environments (in contrast with case expressions)}

\subsubsection{Recursive let bindings}

\subsection{Case Expressions\label{sec:lc-case-exps}}

\todo[inline]{Case expressions are the means by which we do evaluation and
pattern matching -- when things are scrutinized, we evaluate them (if they
aren't evaluated -- tag is 0), and then compare the result against multiple
alternatives}

\todo[inline]{When things are evaluated, that's when consumption of resources
really happen. For example, closing a handle is only closed when we pattern
match on the result of closing the handle (a state token). This means two things
}
\todo[inline]{Item 1. Pattern matching on an expression in WHNF does no computation, so no resources are used}
\todo[inline]{Item 2.
    Pattern matching an expression that is evaluated will not consume all
    the resources that define that computation -- because of laziness, we only
    evaluate things to WHNF. To fully consume a value, we need to consume all
    the linear components of that pattern.
}

\todo[inline]{In practice, we can't know which resources are consumed by
evaluating a given expression. The resources become in a limbo state -- they
cannot be used directly because they might have been consumed, but they 
mustn't be considered as consumed, because they might not have been.  We say
these resources enter a proof irrelevant state. They must still be tracked as
though they weren't consumed, but they cannot be used directly to construct the
program. How can we ensure these proof irrelevant resource variables are fully
consumed? With usage environments -- for the case binder and for the pattern
variables, and otherwise propagate}

\todo[inline]{The trick here is to separate the case rules into two separate
rules, one that fires when the scrutinee is in WHNF, the other when it isn't.}

\todo[inline]{The case binder and pattern variables will consume the scrutinee
resources, be those irrelevant or relevant resources}

\subsubsection{Branching on WHNF-ness}
\subsubsection{Proof irrelevant resources}
\subsubsection{Splitting and tagging fragments}

\TypingRules
\TypingRulesOther

\subsection{Linear Core Examples}

\todo[inline]{Copy over examples from Linear Mini-Core. The ones in the last
section, but also the ones in 2.2 e.g.}

\subsection{Conclusion}

Concluding, $\dots$


% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% {{{ Metatheory
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Metatheory}

\todo[inline]{Consider making type safety and optimizations a section of their
own, so we can have a reverse-binder-swap subsection}

\subsection{Type safety}

\todo[inline]{We proved soundness of our system...}
\todo[inline]{The harder cases are for the interesting ones - lets, cases, and case alternatives}

\TypePreservationTheorem
\ProgressTheorem
\WHNFConvSoundness
\DeltaLinearRelationLemma
\DeltaUnrestrictedRelationLemma
\LinearSubstitutionLemma
\LinearSubstitutionAltsLemma
\UnrestrictedSubstitutionLemma
\UnrestrictedSubstitutionAltsLemma
\DeltaSubstitutionLemma
\DeltaSubstitutionAltsLemma

%\input{language-v4/proofs/TypePreservationTheorem}
%
%\input{language-v4/proofs/ProgressTheorem}
%
%\input{language-v4/proofs/DeltaLinearLemma}
%
%\input{language-v4/proofs/LinearSubstitutionLemma}
%
%\input{language-v4/proofs/UnrestrictedSubstitutionLemma}
%
%\input{language-v4/proofs/DeltaSubstitutionLemma}
 
TODO! Substitution of proof-irrelevant linear variables preserves typing. The
term always remains the same because $x$ cannot occur in any term, however, all
variables that refer to $x$ in their usage environment must now refer the usage env. of the substitee (e.g. $[x] => [\D]$).
This seems trivial to see correct, since all occurrences are in environments, so we get some equivalence similar to the one we need for the proof of Alt0.

TODO: Multiplicity substitution preserves typing lemma

TODO: Canonical forms lemma

TODO: Corollary of $\Delta$-var subst. for $\ov{\Delta}$

TODO: Constructor app typing:
If $\Gamma, \Delta \vdash K~\ov{e}$ and $K{:}\ov{\sigma\to\pi}~T~\ov{p} \in \Gamma$ and $\hasnolinearvars{\Gamma}$
then $\ov{\Gamma, \Delta_i \vdash e_i : \sigma_i}$

\subsection{Core-to-Core optimisations preserve linearity}

We proved multiple optimizing transformations preserve linearity...

\subsubsection{Inlining}

To the best of our knowledge, there is no linear type system for which inlining
preserves linearity\footnote{https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0111-linear-types.rst\#id90}

\InliningTheorem

\subsubsection{\texorpdfstring{$\beta$}{Beta}-reduction}

\BetaReductionTheorem

\BetaReductionSharingTheorem

\BetaReductionMultTheorem

\subsubsection{Binder Swap}

\BinderSwapTheorem

\subsubsection{Reverse Binder Swap Considered Harmful}

(Link to ticket)

\begin{tabbing}
(1) All optimisations preserve (semantic) linearity\\
(2) If a function is (semantically) linear, then we can evaluate it using call-by-name and preserve linearity\\
(3) Reverse binder swap is an optimisation\\
(4) If reverse binder swap is applied to a case scrutinizing a linear resource in the body (`e`) of a linear function `f`, then the function is still linear by (1)\\
(5) If we evaluate `f`, we do it call-by-name because of (2)\\
(6) Call-by-name substitution of the linear argument in the body of a function has been reverse binder swapped doesn’t preserve linearity\\
(7) Contradiction: By 3 and 1, `f` is linear after reverse-binder-swap. By 2, we can substitute arguments to `f` call-by-name and preserve linearity, which contradicts with 6 that says call-by-name substitution after reverse binder swap violates linearity\\
\end{tabbing}

Conclusion:
Either we need to forfeit that we can always substitute call-by-name linear
function applications, or we forfeit that reverse binder swap preserves
linearity (instead, it preserves a weaker notion of linearity understood by the
syntatic-occurrence-analyzer)

\todo[inline]{Reverse-binder-swap is only well-defined in certain scenarios
where the optimizations don't apply call-by-name beta-reduction after the
reverse-binder-swap optimization -- otherwise we would duplicate resources.
In this case, it is not a matter of syntatic vs semantic linearity
}

\todo[inline]{On the reverse binder swap, mention
From Call-by-name, call-by-value, call-by-need and the linear lambda calculus:
The call-by-name calculus is not entirely suitable for reasoning about
functional programs in lazy languages, because the beta rule may copy the
argument of a function any number of times. The call-by-need calculus uses a
diferent notion of reduction, observationally equivalent to the call-by-name
calculus. But call-by-need, like call-by-value, guarantees that the argument
to a function is not copied before it is reduced to a value.
}

It's also interesting to note that reverse-binder-swap preserves linearity under pure call-by-need but not under call-by-name, because
(In the sense that if EVEN linear functions reduce call-by-need rather than call-by-name, then it would preserve optimisations)

Reduce call-by-name linear function application
\begin{code}
f y = (\x. case x of _ -> x:1) (h y)
===>
f y = (case x of _ -> x)[h y/x]
===>
f y = (case h y of _ -> h y) -- consume y twice.
\end{code}

Vs. call-by-need
\begin{code}
 (\y = (\x. case x of _ -> x:1) (h y)) e
===>
    let y = e in
       let x = h y in
        case x of _ -> x
===>
       let x = h e_v in
        case x of _ -> x
===>
        case x_v of _ -> x_v
\end{code}

\subsubsection{Let floating}

\FloatInTheorem
\FullLazinessTheorem
\LocalTransformationsTheorem

\subsubsection{Case of Known Constructor}

\CaseOfKnownConstructorTheorem

\subsubsection{Case of Case}

\CaseOfCaseTheorem

% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% {{{ Syntax Directed System
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Syntax Directed System}

\todo[inline]{In the other system we assume that the recursive lets are strongly connected, i.e. the expressions always}

\input{language-v4/SyntaxDirectedSystem}

\subsection{Inferring usage environments}

\todo[inline]{The difference between this and the previous section is a bit blurry}

\todo[inline]{There's one more concern: usage environments aren't readily
available, especially in recursive lets. We must perform inference of usage
environments before we can typecheck using them. This is how:}

\todo[inline]{Rather, we define a syntax directed type system that infers usage environments while checking...}

% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% {{{ Chapter: Linear Core as a GHC Plugin; Introduction
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\chapter{Linear Core as a GHC Plugin}

This section discusses the implementation of Linear Core as a GHC Plugin, with
a dash of painful history in the attempt of implementing Linear Core directly
into GHC

% Introduction...

\section{Consuming tagged resources}

As discussed in Section~\ref{}, constructor pattern bound linear variables are
put in the context with a \emph{tagged} usage environment with the resources of
the scrutinee. In a \emph{tagged} usage environment environment, all resources
are tagged with a constructor and an index into the many fields of the
constructor.

In practice, a resource might have more than one tag. For example, in the following
program, after the first pattern match, |a| and |b| have, respectively, usage
environments $\{\lctag{x}{K_1}\}$ and $\{\lctag{x}{K_2}\}$:
\begin{code}
f x = case x of
       K a b -> case a of
        Pair n p -> (n,p)
\end{code}
However, in the following alternative, |n| has usage environment
$\{\lctag{\lctag{x}{K_1}}{Pair_1}\}$ and |p| has
$\{\lctag{\lctag{x}{K_1}}{Pair_2}\}$. To typecheck
|(n,p)|, one has to $Split$ |x| first on |K| and then on |Pair|, in order for
the usage environments to match.

In our implementation, we split resources on demand (and don't directly allow
splitting linear resources), i.e. when we use a tagged resource we split the
linear resource in the linear environment (if available), but never split otherwise.
%
Namely, starting on the innermost tag (the closest to the variable name), we
substitute the linear resource for its split fragments, and then we iteratively
further split those fragments if there are additional tags.
%
We note that it is safe to destructively split the resource (i.e. removing the
original and only leaving the split fragments) because we only split resources
when we need to consume a fragment, and as soon as one fragment is consumed
then using the original ``whole'' variable would violate linearity.

In the example, if |n| is used, we have to use its usage environment, which in
turn entails using $\lctag{\lctag{x}{K_1}}{Pair_1}$, which has two tags. In this order, we:
\begin{itemize}
\item Split $x$ into $\lctag{x}{K_1}$ and $\lctag{x}{K_2}$
\item Split $\lctag{x}{K_1}$ and $\lctag{x}{K_2}$ into
  \begin{itemize}
  \item $\lctag{\lctag{x}{K_1}}{Pair_1}$ and $\lctag{\lctag{x}{K_1}}{Pair_2}$
  \item Leave $\lctag{x}{K_2}$ untouched, as we only split on demand, and we aren't using a fragment of $\lctag{x}{K_2}$.
  \end{itemize}
\item Consume $\lctag{\lctag{x}{K_1}}{Pair_1}$, the usage environment of $n$, by removing it from the typing environment.
\end{itemize}


% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\chapter{More ToDos}

\begin{itemize}
\item We know the case binder to ALWAYS be in WHNF, perhaps there could
be some annotation on the case binder s.t. we know nothing happens when we
scrutinize it as a single variable

\item Should we discuss this? It would be fine, but we're not able to see this because of call-by-name substitution
\begin{code}
f x = case x of z { _ -> x }
\end{code}

\item Generalizing linearity section...

\item We kind of ignore the multiplicity semiring. We should discuss
how we don't do ring operations ... but that's kind of wrong.
\end{itemize}


% vim: fdm=marker foldenable
