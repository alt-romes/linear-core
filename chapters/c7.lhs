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
% {{{ Deleted Intro: A Type System for Semantic Linearity in Core; Introduction
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%\chapter{A Type System for Semantic Linearity in Core}
%%%%%
%%%%%A linear type system statically guarantees that linear resources are consumed
%%%%%\emph{exactly once}.
%%%%%%
%%%%%Even though linear types exist 
%%%%%Linear Haskell brings the promises of linear types to the Haskell.
%%%%%%, and is available in the Glasgow Haskell Compiler (GHC) starting from version 9.0.
%%%%%%
%%%%%With linear types, programmers can create powerful abstractions that enforce
%%%%%certain resources are used linearly, such as file handles or allocated
%%%%%memory.
%%%%%%
%%%%%
%%%%%
%%%%%\begin{itemize}
%%%%%\item Linear types are unique in Haskell because of laziness! (amongst some other things)
%%%%%
%%%%%\item For example: trivial linear haskell program
%%%%%
%%%%%\item GHC desugars Linear Haskell into an intermediate language called Core, a
%%%%%System FC, and then applies multiple so-called Core-to-Core optimising
%%%%%transformations in succession.
%%%%%
%%%%%\item For example: some simple inlining
%%%%%
%%%%%\item Linear functions are likewise optimised by the compiler but, crucially,
%%%%%the optimisations must preserve linearity! It would indeed be disastrous if the
%%%%%compiler discarded or duplicated resources such as a file handle or some allocated memory.
%%%%%
%%%%%\item From the above example, consider |x| linear. It might seem as though |x|
%%%%%is being used twice, but since Core's evaluation strategy is call-by-need, we
%%%%%will only evaluate the let when the value is required, and since after
%%%%%optimisation it is never used, we'll never compute the value and thus never use the resource
%%%%%
%%%%%\item In essence, in a lazy language such as Haskell, there's a mismatch
%%%%%between syntactic and semantic linearity, with the former referring to
%%%%%syntactic occurrences of a linear resource in the program text, and the latter
%%%%%to whether the program consumes the resource exactly once in a semantic sense,
%%%%%accounting for the evaluation strategy such as in the let example above.
%%%%%
%%%%%\item The problem: Core is not aware of this. Its linear type system is still
%%%%%very naive, in that it doesn't understand semantic linearity, and will reject
%%%%%most transformed linear programs, since often transformations turn programs
%%%%%that are syntactically linear to programs that are only semantically linear.
%%%%%
%%%%%\item Despite using Core's type system to validate the implementation
%%%%%of the optimising transformations preserve types (and all their combinations),
%%%%%we don't use the Core's linear type system to validate whether the
%%%%%optimisations and their implementation preserves \emph{linearity}. We
%%%%%only \emph{think} that the current optimisations preserve linearity, but we
%%%%%don't check it.
%%%%%
%%%%%\item Understanding semantic linearity isn't trivial, and, in fact, we aren't
%%%%%aware of any linear type system that accounts for non-strict evaluation
%%%%%semantics besides our own.
%%%%%
%%%%%\item We develop a linear type system for Core that understands semantic
%%%%%linearity. We prove the usual preservation and progress theorems with it, and
%%%%%then prove that multiple optimisations preserve types With it, we can accept
%%%%%all intermediate programs GHC produces while applying Core-to-core optimising
%%%%%transformations.
%%%%%
%%%%%\item We implemented a GHC plugin that validates every Core program produced by
%%%%%the optimising pipeline using our type system
%%%%%
%%%%%\item Contributions (ref section for each):
%%%%%\begin{itemize}
%%%%%\item We explain and build intuition for semantic linearity in Core programs by example
%%%%%\item We present a linear type system for call-by-need Core which understands
%%%%%all axis of semantic linearity we previously exposed; and we prove type
%%%%%safety of that system
%%%%%\item We prove that multiple Core-to-core optimising transformations preserve linearity +
%%%%%types under the type system; and discuss 
%%%%%\item We develop a GHC plugin that checks all intermediate Core programs using
%%%%%our type system
%%%%%\end{itemize}
%%%%%
%%%%%\item Somewhere add a stronger case for controlling program optimisations (see 7.1 of Linear Haskell) with linearity
%%%%%\item Somewhere say we build on linear haskell?
%%%%%
%%%%%\end{itemize}
%%%%%
%%%%%\todo[inline]{The introduction needs a lot of motivation!}
%%%%%
%%%%%\todo[inline]{
%%%%%    Inicío deve motivar o leitor, e temos de explicar qual é o problema da
%%%%%    linearidade sintatica em Haskell (vs semantica), e a interação disso com o
%%%%%    call-by-need/lazy evaluation. Quase como se fosse um paper.
%%%%%}
%%%%%
%%%%%\todo[inline]{Compiler optimizations put programs in a state where linearity
%%%%%mixed with call-by-need is pushed to the limits. That is, the compiler
%%%%%preserves linearity, but in a non-trivial semantic way.}
%%%%%
%%%%%\todo[inline]{We present a system that can understand linearity in the presence
%%%%%of lazy evaluation, and validate multiple GHC core-to-core optimizations in
%%%%%this system, showing they can preserve types in our system where in the current
%%%%%implemented Core type system they don't preserve linearity.}
%%%%%
%%%%%\todo[inline]{Note that programmers won't often write these programs in which
%%%%%let binders are unused, or where we pattern match on a known constructor -- but
%%%%%these situations happen all the time in the intermediate representation of an
%%%%%optimising compiler $\dots$}

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
%optimising transformations with regard to linearity just as Core does for types
%-- a linearly typed Core ensures that linearly-typed programs remain correct
%both after desugaring and across all GHC optimising transformations,
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
%% desugaring and optimising transformations, because linearity is seemingly
%% violated.
%%
%The current solution to valid programs being rejected by Core's linear
%type-checker is to effectively disable the linear type-checker since,
%alternatively, disabling optimising transformations which violate linearity
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

%%%%\todo[inline]{Continue introduction}
%%%%
%%%%Our contributions are (to rewrite):
%%%%\begin{itemize}
%%%%\item We expose a connection between the definition of \emph{consuming} a
%%%%resource in a linear type system and with the fundamental definition of
%%%%\emph{evaluation/progress} and the evaluation strategy of a language, making
%%%%the \emph{consuming} more precise across languages (in fact, generalizing the
%%%%definition of consuming a resource from Linear Haskell).
%%%%% \item We present a linear type system that can leverage this connection to be
%%%%% more flexible and allow more programs as linearly well-typed.
%%%%% \item This type system is defined over a language capturing the linear essence of Core
%%%%% \item We prove soundness and that Core optimisations preserve types in this system, where they previously were unable to
%%%%\end{itemize}

% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% {{{ Linearity, Semantically
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Linearity, Semantically\label{sec:linearity-semantically}}

A linear type system statically guarantees that linear resources are
\emph{consumed} exactly once. Consequently, whether a program is well-typed
under a linear type system intrinsically depends on the precise definition of
\emph{consuming} a resource. Even though \emph{consuming} a resource is
commonly regarded as synonymous with the \emph{syntactic occurrence} of the resource
in the program, that is not always the case.
%
In fact, this chapter highlights the distinction between using resources
\emph{syntactically} and \emph{semantically} as a principal limitation of
linear type systems for non-strict languages, with examples motivated by the
constructs available in GHC Core and how they are evaluated.

% and we show how a linear type system found on
% \emph{consuming resources semantically} rather than \emph{using resources
% syntactically} can accept

Consider the following program in a functional Haskell-like language,
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
of the language, the computation that closes the handle might or not be
evaluated, and if it isn't, the |handle| in that unused computation
is not consumed.
%
Expanding on this, consider the above example program under distinct
evaluation strategies:
%
\begin{description}

\item[Call-by-value] With \emph{eager} evaluation semantics, the let bound expression |close
handle| is eagerly evaluated, and the |handle| will be closed before being
returned. It is clear that a linear type system should not accept such a
program since the linear resource |handle| is duplicated -- it is used in a
computation that closes it, while still being made available to the caller of
the function.

\item[Call-by-need] On the other hand, with \emph{lazy} evaluation semantics, the let
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

From this observation, and exploring the connection between computation and evaluation,
% \todo{Alguma dificuldade em dizer exatamente como é que evaluation drives/is computation}
it becomes clear that \emph{linearity} and \emph{consuming resources}, in the
above example and for programs in general, should be defined in function of the
language's evaluation strategy.
%
We turn our focus to \emph{linearity} under \emph{call-by-need}, not only
because GHC Core is \emph{call-by-need}, but also because the distinction
between semantically and syntactically consuming a resource is only exposed
under \emph{non-strict} semantics.
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

\section{Semantic Linearity by Example\label{sec:semantic-linearity-examples}}

Aligned with our original motivation of typechecking linearity in GHC Core such
that optimising transformations preserve linearity, and with the goal
of understanding linearity in a non-strict context, this section helps the
reader build an intuition for semantic linearity through examples of Core
programs that are semantically linear but rejected by Core's linear type
system.
% BETTER?:
%Aligned with our motivation of typechecking linearity in GHC Core such
%that optimising transformations preserve linearity, and in order to explain
%linearity in a non-strict context, we illustrate semantic linearity
%through examples of Core programs that are semantically linear but rejected by
%Core's linear type system -- building intuition towards semantic linearity in a
%lazy language.
%
In the examples, a \colorbox{working}{\workingcolorname} background highlights programs that are
syntactically linear and are accepted by Core's naive linear type system. A
\colorbox{notyet}{\notyetcolorname} or \colorbox{limitation}{\limitationcolorname} background mark programs that are
semantically linear, but are not seen as linear by Core's (naive wrt laziness) linear type
system. Notably, the linear type system we develop in this work accepts all
\colorbox{notyet}{\notyetcolorname} programs.
% (while the few \colorbox{limitation}{\limitationcolorname} programs are not accepted).
A \colorbox{noway}{\nowaycolorname} background indicates that the program
simply isn't linear, not even semantically, i.e. the program effectively
discards or duplicates linear resources.

\subsection{Let bindings}
We start our discussion with non-strict (non-recursive) let bindings, i.e. let bindings whose
body is evaluated only when the binding is needed, rather than when declared.
In Core, a let binding entails the creation of a \emph{thunk} that suspends the
evaluation of the let body (for background, see
Section~\ref{sec:background:evaluation-strategies}). When the binding itself is evaluated, the \emph{thunk} is
\emph{forced} and the evaluation is carried out. The result overwrites the
\emph{thunk} -- the let binding now points to the result of the evaluation.
% A \emph{thunk} is \emph{forced} (and the suspended computation is evaluated) when
% the binding itself is evaluated.

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
According to Linear Haskell's core calculus~$\lambda_{\to}^{q}$~\cite{cite:linearhaskell}, let
bound variables are annotated with a multiplicity which is multiplied (as per
the multiplicity semiring) by the multiplicity of all variables that are free
in the binder's body.
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
body, however, the resource is still used semantically linearly because |y| isn't used at all, thus |x| is consumed just once in the let body:
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

% \parawith{Summary}
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

\subsection{Recursive let bindings\label{sec:semantic-linearity-examples:recursive-lets}}
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
\item And if the binding $x$ is fully evaluated, then all resources in $\Delta$ are consumed exactly once.
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

% \parawith{Summary}
Summarising, recursive let bindings behave like non-recursive let bindings in
that if they aren't consumed, the resources they depend on aren't consumed
either.  However, recursive let bindings are defined in terms of themselves, so
the set of linear resources that will be consumed when the binder is evaluated
is also defined in terms of itself (we need it to determine what resources are
used when we recurse). We can intuitively think of this set of linear resources
that will be consumed as a solution to a set of equations defined by a group of
mutually recursive bindings, which we are able to reason about without an
algorithm for simpler programs. In our work, the core type system isn't
concerned with deriving said solution, but we present a simple algorithm for
inferring it with our implementation.

\subsection{Case expressions}

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
expressions.

%%% In Section~\ref{sec:generalizing-evaluation-consuming} we generalize the idea
%%% that consuming a resource is deeply tied to evaluation.  Here, we continue
%%% building intuition for semantic linearity, first reviewing how case expressions
%%% evaluate expressions, and then exploring how they consume resources, by way of example.

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
By forcing the pattern variable (or the let binding), we run the computations
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

However, we must also consider pattern matches on constructors without
any linear components. If the constructor has no linear fields, it means the
result can be consumed unrestrictedly and, therefore, all linear resources used
in the computation have been fully consumed.
%
Consequently, in a branch of a constructor without linear fields we know the
result of evaluating the scrutinee to be unrestricted, so we can use the case
binder unrestrictedly and refer to it zero or more times. For example, this
program is semantically linear:
\begin{notyet}
\begin{code}
f16 :: () ⊸ ()
f16 x = case x of z { () -> z <> z }
\end{code}
\end{notyet}
A second example of an unrestricted pattern, where |K2| has no fields and |K1|
has one linear field, seems as though it shouldn't typecheck since the resource
$x$ must have been fully consumed to take the |K2| branch, but because the
scrutinee is known to be |K1|, the |K2| branch is \emph{absurd}, so, in reality
any resource could be freely used in that branch, and the example is
\emph{semantically} linear (despite not being seen as so by our system):
%
\begin{limitation}
\begin{code}
f :: a ⊸ a
f x = case K1 x of z { K2 -> x; K1 a -> x }
\end{code}
\end{limitation}
%
This particular example has a known constructor being scrutinized which might
seem like an unrealistic example, but we recall that during the transformations
programs undergo in an optimising compiler, many programs such as this
naturally occur (e.g. if the definition of a function is inlined in the
scrutinee).
%
% However, the scrutinee before evaluation likely isn't in WHNF, thus scrutinee
% resources cannot directly occur in the case alternatives, since they might be
% potentially consumed when evaluating the scrutinee, the program leading up to
% this one wouldn't have been linear (even semantically).

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

Before last, we consider the default case alternatives, also known as wildcards
(written $\_$), in the presence of linearity: matching against the wildcard
doesn't provide new information, so linearity is seen as before but without
fully consuming the scrutinee linear resources (in non-linear patterns) nor
binding new linear resources (in linear patterns). In short, if the scrutinee
is in WHNF, we can either use the resources from the scrutinee or the case
binder in that alternative, if the scrutinee is not in WHNF, we \emph{must} use
the case binder, as it's the only way to linearly consume the result of
evaluating the scrutinee.

Finally, we discuss the special case of a case expression scrutinizing a
variable $x$:
\[
\lambda x.~\ccase{x}{\_ \to x}
\]
It might seem as though the program is linear:
\begin{itemize}
\item If $x$ is in WHNF, then scrutinizing it is a no-op, and returning $x$
just returns the resource intact.
\item If $x$ is not in WHNF, then scrutinizing it evaluates it to WHNF, and
returning $x$ returns the result of evaluating $x$ that still had to be
consumed exactly once.
\end{itemize}
However, in practice, it depends on the evaluation strategy. If linear function
applications are $\beta$-reduced \emph{call-by-name} (a common practice, as
linear functions use their argument exactly once), and the above function is
considered linear, then an application might duplicate linear resources during
evaluation. For example:
\[
\begin{array}{l}
(\lambda x.~\ccase{x}{\_ \to x})~(free~x)\\
\Longrightarrow_{CBN~\beta-reduction}\\
\ccase{free~x}{\_ \to free~x}
\end{array}
\]
Therefore, the type system we present in the next section, which evaluates
linear applications call-by-name, does not accept the above program as linear.
Foreshadowing, this particular interaction between evaluation and linearity
comes up in the type preservation proof of our program, and is again explored
with the reverse binder swap transformation in
Section~\ref{sec:optimisations-preserve-types-meta}.

% \parawith{Summary}
In summary, case expressions evaluate their scrutinees to WHNF,
introduce a case binder, and bind pattern variables. If the scrutinee is
already in WHNF, all resources occurring in it are still available in the case
alternative, alongside the case binder and the pattern-bound variables. In the
case alternative, either the resources of the scrutinee, the case binder, or
the linearly bound pattern variables must be used exactly once, but mutually
exclusively. For scrutinees not in WHNF, in the case alternative, either the
case binder or the linear pattern variables need to be used, in mutual exclusion.
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

% ROMES: We don't have time to do this I think
%%%\subsection{Generalizing linearity in function of evaluation\label{sec:generalizing-evaluation-consuming}}
%%%
%%%\todo[inline]{Deixar isto para último, dificil generalizar, se necessario cortar}
%%%
%%%Indeed, as hinted towards in the previous section, there's a deep connection
%%%between \emph{evaluation} and \emph{consuming resources}.
%%%
%%%Definition X.Y: A linear resource is consumed when it is either fully evaluated
%%%(NF) to a value, or when it is returned s.t. an application of that function
%%%being fully evaluated would fully evaluate the resource to a value. Or something like that.
%%%%
%%%Note how this generalizes Linear Haskell's definition of consuming a resource: $\dots$
%%%
%%%\begin{itemize}
%%%\item We could almost say that eventually everything all linear
%%%resources must be evaluated to NF to be consumed, or returned by a function
%%%s.t. a continuation of that function has to evaluate the result to NF., or something.
%%%
%%%\item Discuss our own generalized (call-by-value, call-by-name, etc)
%%%definition of consuming resources by evaluation. Something like, if an
%%%expression is fully evaluated, all linear resources that expression depends on
%%%to compute a result are consumed, or something...
%%%
%%%\item How does this relate to strictness? Reference the section of Linear
%%%Haskell about linearity and strictness, and basically revisit what they say.
%%%
%%%\end{itemize}
  

% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% {{{ Linear Core
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{A Type System for\\ Semantic Linearity in Core\label{sec:main:linear-core}}
\chaptermark{A Type System for Semantic Linearity in Core}

In this chapter, we develop a linear calculus $\lambda_\Delta^\pi$, dubbed \emph{Linear Core}, that 
combines the linearity-in-the-arrow and multiplicity polymorphism introduced by
Linear Haskell~\cite{cite:linearhaskell} with all the key features from GHC's Core
language, except for type equality coercions\footnote{We explain a main avenue of
future work, multiplicity coercions, in Section~\ref{sec:future-work}}.
%
Specifically, our core calculus is a linear lambda calculus with algebraic
datatypes, case expressions, recursive let bindings, and multiplicity
polymorphism.

Linear Core makes much more precise the various insights discussed in the
previous chapter by crystallizing them together in a linear type system for which we
prove soundness via the usual preservation and progress theorems. Crucially,
the Linear Core type system accepts all the \emph{semantically linear} example
programs (highlighted with \colorbox{notyet}{\notyetcolorname})
from Section~\ref{sec:semantic-linearity-examples}, which Core currently
rejects.
%
Besides type safety, we prove that multiple optimising Core-to-Core
transformations preserve linearity in Linear Core. These same transformations
don't preserve linearity under Core's current type system. As far as we know,
we are the first to prove optimisations preserve types in a non-strict linear
language.

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
other non-strict languages.

We present Linear Core's syntax and type system iteratively, starting with the
judgements and base linear calculi rules for multiplicity and term lambdas plus
the variable rules ($\S~\ref{sec:base-calculi}$).
%
Then, usage environments, the rule for $\Delta$-bound variables, and rules for
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

\section{Language Syntax and Operational Semantics}

The complete syntax of Linear Core is given by Figure~\ref{fig:full-linear-core-syntax}.
% Figure~\ref{fig:linear-core-types} and Figure~\ref{fig:linear-core-terms}.
%
The types of Linear Core are algebraic datatypes, function types, and
multiplicity schemes to support multiplicity polymorphism: datatypes
($T~\ov{p}$) are parametrised by multiplicities, function types
($\vp\to_\pi\s$) are also annotated with a multiplicity, which can be $1$,
$\omega$ (read \emph{many}), or a multiplicity variable $p$ introduced by a
multiplicity universal scheme ($\forall p.~\vp$).
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
all~\cite{cite:minicore}, which first tentatively tackled Core's
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

The (small-step) operational semantics of Linear Core are given by
Figure~\ref{fig:linear-core-operational-semantics}. We use call-by-name
evaluation for Linear Core as it captures the non-strict semantics in which
our type system understands linearity, while being simpler to reason about than
call-by-need operational semantics.
% which is traditionally modelled with a
% mutable heap to store \emph{thunks} and the values they are overwritten with.
Furthermore, linear function applications, even in a \emph{call-by-need} system, are
usually reduced \emph{call-by-name} as the function argument is guaranteed to
be used exactly once (thus avoiding unnecessarily allocating memory on the heap
for a redundant \emph{thunk}).
%
Specifically, function applications are reduced by the standard
\emph{call-by-name} $\beta$-reduction, substituting the argument whole by
occurrences of the lambda binder in its body, case expressions evaluate their
scrutinee to WHNF, substituting the result by the case binder and constructor
arguments for pattern-bound bound variables matching on that same constructor.

\input{language-v4/OperationalSemantics}

\section{Typing Foundations\label{sec:base-calculi}}

Linear Core ($\lambda^\pi_\Delta$) is a linear lambda calculus akin to Linear
Haskell's $\lambda^q_\to$ in that both have multiplicity polymorphism,
(recursive) let bindings, case expressions, and algebraic data types.
$\lambda^\pi_\Delta$ diverges from $\lambda^q_\to$ primarily when typing lets,
case expressions, and alternatives (in its purpose to type semantic linearity).
%, and secondarily in only treating multiplicity polymorphism superficially.
%
% \todo{And our treatment of multiplicity polymorphism completely ignores
% algebraic treatment of multiplicities with semiring operations!!! Would it be
% sufficient to add a rule for application of variable multiplicity functions?}
%
Otherwise, the base rules of the calculus for, multiplicity and term,
abstraction and application are quite similar. In this section, we present
the linear calculi's typing rules that share much in common with
$\lambda^q_\to$, and, in the subsequent sections, the rules encoding the
novel insights from Linear Core in typing semantic linearity, that were
explored by example in Section~\ref{sec:linearity-semantically}.
%
We note, however, that we handle multiplicity polymorphism differently from
Linear Haskell in ignoring the multiplicity semiring and, instead,
conservatively treating all multiplicity polymorphic functions as linear.
%
The full type system is given by Figure~\ref{fig:linear-core-typing-rules},
with auxiliary judgements given by
Figure~\ref{fig:linear-core-other-judgements}.

\TypingRules
\TypingRulesOther

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
The main typing judgement reads ``expression $e$ has type $\s \to \vp$ under
the unrestricted environment $\G$ and linear environment $\D$'':
\[
\G;\D \vdash e : \s \to \vp
\]
Occurrences of unrestricted variables from $\G$ are well-typed as long as the linear
environment is empty, while occurrences of linear variables are only well-typed
when the variable being typed is the only resource available in the linear context.
\[
\begin{array}{cc}
\TypeVarOmega & \TypeLinearVar
\end{array}
\]
In both cases, the linear context must contain exactly what is required to
prove the proposition, whereas the unrestricted context may contain arbitrary
variables.
%
Variables in contexts are annotated with their type and multiplicity, so
$\x[\pi]$ is a variable named $x$ of type $\s$ and multiplicity $\pi$.

Linear functions are introduced via the function type ($\s \to_\pi \vp$) with
$\pi = 1$, i.e. a function of type $\s \to_1 \vp$ (or, equivalently, $\s \lolli \vp$)
introduces a linear resource of type $\s$ in the linear environment $\D$ to then type an expression of type $\varphi$.
%
Unrestricted functions are introduced via the function type ($\s \to_\pi \vp$) with $\pi =
\omega$, and the $\lambda$-bound variable is introduced in $\G$:
\[
\begin{array}{cc}
\TypeLamIntroL & \TypeLamIntroW
\end{array}
\]
A linear function application is well-typed if there exists a disjoint split of the
linear resources into $\D,\D'$ s.t. the function and argument, each under a
distinct split, are both well-typed and the argument type matches the
function's expected argument type. Conversely, unrestricted resources are
duplicated and available whole to both sub-derivations.
\[
\TypeLamElimL
\]
An unrestricted function, unlike a linear one, consumes its argument
unrestrictedly (zero or more times). Therefore, in an unrestricted function
application, allowing any linear resources to occur in the argument expression
entails consuming those resources unrestrictedly, since the
variable binding the argument expression could be discarded or used more than
once in the function body. Thus, argument expressions to unrestricted functions must also
be unrestricted, i.e. no linear variables can be used to type them.
\[
\TypeLamElimW
\]
Typing linear and unrestricted function applications separately is less general
than typing applications of functions of any multiplicity $\pi$ by scaling (per the multiplicity
semiring) the multiplicities of the resources used to type the argument by $\pi$, however, our objective of typing semantic
linearity does not benefit much from doing so, and by keeping the simple approach we can have
the linear and unrestricted environments be separate.
% \todo{We might only need multiplicities for the case-of-case definition as it
% exists in ghc?, even then couldn't we do semiring scaling without variables?
% Also, dislike sentence}

Multiplicity abstractions ($\Lambda p.~e$) introduce a multiplicity variable
$p$ (in the unrestricted context), and construct expressions of type
$\forall p.~\dots$, i.e. a type universally quantified over a multiplicity
variable $p$. We note that, in the body of the abstraction, function types annotated
with a $p$ variable and datatype fields with multiplicity $p$ are typed as
thought they are linear functions and linear fields, because $p$ can be
instantiated at both $\omega$ and $1$ (so types using $p$ must be well-typed at both instantiations).
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
The rule additionally requires that $\pi$ be \emph{well-formed} in order
for the expression to be well-typed, using the judgement $\G \vdash_{mult}
\pi$, where well-formedness is given by $\pi$ either being $1$, $\omega$, or an
in-scope  multiplicity variable in $\G$.
\[
\TypeWellFormedMult
\]

These rules conclude the foundations of our linear calculi. In subsequent
sections we type (recursive) let bindings and case expressions,
accounting for semantic linearity as per the insights construed in
Section~\ref{sec:linearity-semantically}, effectively distilling them into the
key ideas of our work -- encoded as rules.


\section{Usage environments\label{sec:usage-environments}}

A \emph{usage environment} $\Delta$ is the means to encode the idea that lazy
bindings don't consume the resources required by the bound expression when
defined, but rather when the bindings themselves are fully consumed.
Specifically, we annotate so-called $\Delta$-bound variables with a \emph{usage
environment} to denote that consuming these variables equates to consuming the
resources in the usage environment $\D$ they are annotated with, where a usage
environment is essentially a multiset of linear resources. $\Delta$-bound
variables are introduced by a handful of constructs, namely, (recursive) let
binders, case binders, and case pattern variables. In the following example, as
per the insights into semantic linearity developed in
Section~\ref{sec:semantic-linearity-examples}, the resources required to
typecheck the body of the binder $u$, $x$ and $y$, are only used if the let-var
$u$ is consumed in the let-body $e$.  Accordingly, the usage environment of
the let-bound $u$ is $\{x,y\}$:
\[
f = \lambda \xl.~\lambda \y[1].~\llet{u = (x,y)}{e}
\]
Furthermore, usage environments guarantee that using a $\Delta$-bound variable
is mutually exclusive with directly using the resources it is annotated with --
using the $\Delta$-bound variable consumes all linear resources listed in its
usage environment, meaning they are no longer available for direct usage.
Dually, using the linear resources directly means they are no longer available
to consume through the usage environment of the $\Delta$-bound variable.

Finally, we note that usage environments bear a strong resemblance to the linear
typing environments to the right of the semicolon in the main typing judgement,
i.e. the environment with the linear resources required to type an expression.
%
In fact, usage environments and linear typing contexts differ only in that the
former are used to annotate variables, while the latter used to type
expressions. Yet, this distinction is slightly blurred after introducing how
typing environments can be moved to usage environments, or otherwise occurs in
rules relating the two.

\subsection{\texorpdfstring{$\D$}{Delta}-bound variables}

A $\Delta$-bound variable $u$ is a variable annotated with a usage environment $\Delta$. Crucially, for any $\Delta$-bound variable $u$:
%
\begin{enumerate}
\item Using $u$ is equivalent to using all the linear resources in $\Delta$
%\item $u$ can only be used once, since the $\D$ resources will not be available afterwards
\item Using $u$ is mutually exclusive with using the $\Delta$ resources it depends on elsehow
\item $u$ can be safely discarded as long as the resources in $\Delta$ are consumed elsehow
\end{enumerate}
%
Fortunately, since linear resources must be linearly split across
sub-derivations, (2) follows from (1): consuming the linear resources
in $\Delta$ to type $u$ makes them unavailable in the context of any other
derivation. Therefore, expressions using these resources a second time, directly, or indirectly through the same
(or other) usage environment, is ill-typed, as the resources are
already allocated to the derivation of $u$. Similarly, (3) also follows from
(1), because if the linear resources aren't consumed in the $\Delta$-var
derivation, they must be consumed in an alternative derivation (or otherwise
the expression is ill-typed).

These observations all boil down to one typing rule for $\Delta$-bound
variables, which fundamentally encodes (1), implying the other two bullets:
\[
\TypeVarDelta
\]
The rule reads that an occurrence of a $\Delta$-bound variable is well-typed if
the linear environment is exactly the resources in the usage environment of
that variable.
% ROMES:TODO: Dizer alguma coisa tipo (blurring the distinction between usage envs and typing envs)?

$\D$-variables are always introduced in $\Gamma$ since they can be discarded
and duplicated, despite multiple occurrences of the same $\Delta$-variable not
possibly being well-typed as, ultimately, it would imply non-linear usage of
linear resources.
% multiple occurrences of the same
% $\D$-variable imply non-linear usage of resources that must be used linearly.


\subsection{Lazy let bindings}

In Section~\ref{sec:semantic-linearity-examples}, we discussed how linear
resources used in let-bound expressions are only consumed when the same let-bound
expressions are fully evaluated, i.e. linear resources required by let-bound
expressions are consumed lazily.
%
Moreover, resources from a let-bound expression cannot be used \emph{together}
with the variable binding, since said resources would end up being consumed
more than once, violating (semantic) linearity -- the binder has to be used in
mutual exclusion with the linear resources required to type the expression it
binds, and either \emph{must} be used, or we'd be discarding resources.

Indeed, usage environments allow us to encode mutual exclusivity between
alternative ways of consuming linear resources (between $\D$-vars and direct
resource usage). Let-bound variables are the canonical example of a
$\Delta$-bound variable, that is, let-variables bind expressions in which
the resources required to type them are consumed lazily rather than eagerly.
%
Effectively, annotating let-bound variables with a usage environment $\D$
\emph{delays} the consumption of resources to when the variables themselves are
used.

Summarily, let-bindings introduce $\Delta$-variables whose usage environments
are the linear typing environments of the bindings' bodies:
\[
\TypeLet
\]
The rule for non-recursive let bindings splits the linear environment in $\D$
and $\D'$. $\D$ is used to type the body $e$ of the let binding $x$. Perhaps
surprisingly, the resources $\D$ used to type $e$ are still available in the
environment to type the let body $e'$, alongside the unrestricted $x$ binding
annotated with the usage environment $\D$. Ultimately, the resources being
available in $e'$ reflects the fact that typing a lazily bound expression
doesn't consume resources, and the binding $x$ being $\D$-bound reflects that
its usage entails consuming the resources $\D$ the expression $e$ it binds depends on.
% \todo[inline]{Let bindings are hard, if they are used then we use resources. If
% they don't get used then we use no resources! In practice, resources that show
% up in the body of the let must be used, be it by using the let binder, or by
% using them directly. This makes the let binder and the resources in its body
% mutual exclusive.}

% \todo[inline]{Explain the idea of suspended computation, and how resources will
% be consumed to some extent when we force the computation -- also foreshadowing
% that evaluation to WHNF doesn't necessarily consume all resources}

\subsection{Recursive let bindings}

Recursive let bindings are very similar to non-recursive ones, the main
exception being that the recursive bindings may be defined in terms of
themselves, and we may have more than one binding. In our system, groups of
recursive let bindings are always assumed to be strongly connected, that is,
all the bindings in a recursive let group are mutually recursive in the sense
that they all (transitively) depend on one another.

As before, recursive let bindings bind expressions \emph{lazily}, so they similarly
introduce a $\D$-variable for each binding, and resources required to type the
let-bindings are still available in the body of the let, to later be consumed
via $\D$-variables or directly, if the let-bindings are unused.
%
However, as shown by example in Section
\ref{sec:semantic-linearity-examples:recursive-lets}, we must consider how
recursive uses of a binder in its own definition entails consuming all resources otherwise
required to type the binder's body.
%, i.e. a least upper bound.
%
Extrapolating to a strongly-connected group of recursive bindings, (mutually)
recursive uses of binders entail consuming all resources
required to type those binders. By definition, those binders in turn
recursively use binders that used them, and thus all the resources otherwise
required to type them.
%
Ultimately, all binders in a strongly-connected group of mutually recursive let
bindings have to be typed with the same linear resources (which are the least
upper bound of resources needed to type the bodies of all binders, accounting
for uses of mutually-recursive binders).
%
% Therefore, we conclude the least upper bound of resources required to type a
% mutually recursive group of let bindings to be the same for any such group that
% is strongly-connected.

The typing rule for recursive groups of bindings leverages our assumption that
all recursive let bindings are strongly connected and exactly the observation
that every binder in a strongly connected group of recursive bindings is typed
with the same linear context. Consequently, all bindings of the recursive group
are introduced as $\D$-vars with the same $\D$ environment -- using any one of
the bindings in a recursive group entails consuming all resources required to
type that same group, which is also why we can use the same linear resources to
type each binder:
\[
\TypeLetRec
\]
Unfortunately, this formulation is ill-suited for a syntax-directed system
(from which an implementation is direct) because determining a particular $\D$
to type and annotate all binders is difficult. We present our system and
metatheory agnostically to the challenge of inferring this linear typing
environment by assuming recursive let expressions are annotated with the
correct typing environment.

In practice, determining this typing environment $\D$ amounts to finding a
least upper bound of the resources needed to type each mutually-recursive
binding that (transitively) uses all binders in the recursive group.
%
We propose a naive algorithm for inferring usage environments of recursive
bindings in Section~\ref{sec:discuss:implementation} orthogonally to the theory
developed in this section.
%
The algorithm is a $O(n^2)$ traversal over the so-called \emph{naive usage
environments} used to type each binding.
%
Inference of usage environments for recursive binding groups bears some
resemblance to the inference of principle types for recursive bindings
traditionally achieved through the Hindley–Milner inference
algorithm~\cite{DBLP:conf/popl/DamasM82}, there might be an opportunity to
develop a better algorithm leveraging existing inference techniques.
%
Despite being a seemingly useful observation, we leave exploring a potential
connection between inference of usage environments and type inference
algorithms as future work.

% We present a naive algorithm for inferring usage environments of recursive bindings in
% Section~\ref{sec:impl:recursive-alg} and leave exploring this potential
% connection as future work.

\section{Case Expressions\label{sec:lc-case-exps}}

Case expressions \emph{drive evaluation} --
% thus they are key to realize a type system that understands linearity in the presence of lazy evaluation.
%
%However, the evaluation of case expressions is considerably nuanced,
%
%In lazy let bindings, computations  can be a case
%expression can effectively consume resources rather than just 
%
a case expression \emph{evaluates its scrutinee} to Weak Head Normal Form
(WHNF)~\cite{10.5555/1096899}, \emph{then} selects the case alternative corresponding to the pattern
matching the Weak Head Normal Form of the scrutinee\footnote{In our calculus,
the alternatives are always exhaustive, i.e. there always exists at least one
pattern which matches the scrutinee in its WHNF, so we're guaranteed to have an
expression to progress evaluation.}. An expression in Weak Head Normal Form can
either be:
\begin{itemize}
\item A lambda expression $\lambda x.~e$,
\item or a datatype constructor application $K~\ov{e}$
\end{itemize}
In both cases, the sub-expressions $e$ or $\ov{e}$ occurring in the lambda body
or as constructor arguments needn't be evaluated for the lambda or constructor
application to be in weak head normal form (if otherwise all sub-expressions
were fully evaluated the whole expression would also be in \emph{normal form}).
% (that is why it is called \emph{weak} head normal form).
%
Accordingly, these sub-expressions might still depend on linear resources to be
well-typed (these resources will be consumed when the expression is evaluated).
%
As will be made clear in later sections, we need to devise a specialized typing
judgement for scrutinees that is able to distinguish between terms
in WHNF and terms that are not in WHNF.
%
Following the discussion on expressions in weak head normal form, we present a
typing judgement $\G;\D \Vdash e : \s \gtrdot \ov{\D_i}$, and a rule for each
of the forms given above:
\[
    \TypeWHNFCons
\qquad
    \TypeWHNFLam
\]
This judgement differs from the main typing judgement in that (1) it only
applies to expressions in weak head normal form, and (2) it ``outputs'' (to the right of $\gtrdot$) a
disjoint set of linear environments ($\ov{\D_i}$), where each environment corresponds to the
linear resources used by a sub-expression of the WHNF expression.
%
To type a constructor application $K~\ov{e_\omega e_i}$, where $e_\omega$
are unrestricted arguments and $e_i$ the linear arguments of the
constructor, we split the resources $\D$ into a disjoint set of resources
$\ov{\D_i}$ required to type each linear argument individually and return exactly
that split of the resources; the unrestricted $e_\omega$ expressions must be
typed on an empty linear environment. A lambda expression is typed with
the main typing judgement and trivially ``outputs'' the whole $\D$ environment,
as there is always only a single sub-expression in lambdas (the lambda body).

Recall that the operational semantics encode the evaluation of case expressions as:
%
\begin{tabbing}
$\ccase{e}{z~\{\ov{\rho_i \to e_i}\}} \longrightarrow^* \ccase{e'}{z~\{\ov{\rho_i \to e_i}\}}$\`where $e'$ is in WHNF and $e$ is not\\
$\ccase{K~\ov{e}}{z~\{K~\ov{x} \to e_i\}} \longrightarrow e_i\ov{[e/x]}[K~\ov{e}/z]$\\
$\ccase{e}{z~\{\_ \to e_i\}} \longrightarrow e_i[e/z]$\`where $e$ is in WHNF\\
\end{tabbing}
%
When a scrutinee $K~\ov{e}$ matches a constructor pattern $K~\ov{\x[\pi]}$,
evaluation proceeds in the case alternative corresponding to the matching
pattern, with occurrences of $\ov{x}$ being substituted by $\ov{e}$, and
occurrences of the case binder $z$ substituted by the whole scrutinee
$K~\ov{e}$. Constructors and lambda expressions otherwise match the wildcard
pattern whose alternative body is evaluated only substituting the case binder by the
scrutinee. 

We highlight that, when evaluating a case expression, computation only
effectively happens when a scrutinee not in WHNF is evaluated to WHNF. When the
scrutinee is already in WHNF, evaluation continues in the alternative by
substituting in the appropriate scrutinee expressions, but without having
performed any computation.
% (the scrutinee was already in weak head normal form).
%In short, no computation happens if the scrutinee is already in WHNF.
%
In terms of linearity, resources are consumed only if evaluation happens.
Therefore, resources used to type a scrutinee not in
WHNF will be consumed when the case is evaluated, making said resources unavailable in the case
alternatives. Conversely, when the scrutinee is already in WHNF, linear
resources required to type the scrutinee are still available in the alternatives.
The linear resources used by an expression in WHNF are exactly those which
occur to the right of $\gtrdot$ in the WHNF judgement shown above
(corresponding to the resources required to typecheck the lambda body or the
constructor arguments).

%Recalling that patterns are either a wildcard that matches anything or data
%constructors parametrised by variables to bind the constructor arguments in the
%case alternative
%
%Let's consider how resources are consumed when the case exp ...
%
%Patterns data constructors with variables to bind the constructor arguments parametrised
%
%\begin{itemize}
%\item The wildcard pattern matches against anything, and is the only pattern that matches against a lambda function
%\item We can match against the data constructor and 
%\end{itemize}
%
%Considering patterns are either data constructors and variables bounding
%A function (lambda expression) can only be matched against the wildcard pattern $\_$, but 
%
%Evaluation continues in the selected branch by
%substituting, first, the pattern variables by the (possibly unevaluated)
%expressions used as arguments to the 

% \todo[inline]{Case expressions are the means by which we do evaluation and
% pattern matching -- when things are scrutinized, we evaluate them (if they
% aren't evaluated -- tag is 0), and then compare the result against multiple
% alternatives}

% \todo[inline]{Item 2.
%     Pattern matching an expression that is evaluated will not consume all
%     the resources that define that computation -- because of laziness, we only
%     evaluate things to WHNF. To fully consume a value, we need to consume all
%     the linear components of that pattern.
% }

\subsection{Branching on WHNF-ness}

The dichotomy between evaluation (hence resource usage) of a case expression
whose scrutinee is in weak head normal form, or otherwise, leads to one of our
key insights: we must \emph{branch on weak head normal formed-ness} to
type case expressions.
%
When the scrutinee is already in weak head normal form, the resources are
unused upon evaluation and thus available in the alternatives.
%
When it is not, resources will be consumed and cannot be used in the
alternative.
%
To illustrate, consider a case expression with a scrutinee in weak head normal
form and another whose scrutinee is not:
\[
\begin{array}{ccc}
(1)~\lambda x.~\ccase{K~x}{\_ \to x} &  & (2)~\lambda x.~\ccase{free~x}{\_ \to x}
\end{array}
\]
The first function uses $x$ linearly, while the second does not.
%
Alternatives may also use the case binder or pattern variables, referring to, respectively,
the whole scrutinee (and all resources used to type the scrutinee) or
constructor arguments (and the resources to type each argument).
% Using the case binder entails using all the resources required by the scrutinee, and using a pattern
% variable implies using the resources of the corresponding constructor argument.

Linear resources must be used exactly once, but there are three \emph{competing} ways
to use the resources from a scrutinee in WHNF in a case alternative: directly, via
the case binder, or by using \emph{all} the pattern-bound variables.
%
Recall how $\D$-variables can encode mutual exclusivity between alternative
ways of consuming resources -- it follows that case binders and pattern-bound
variables are another instance of $\D$-bound variables. Intuitively, resources
in a scrutinee that is already in WHNF are only properly consumed when all
(linear) fields of the pattern are used, satisfying the definition of
consuming resources given in Linear Haskell.
%
% We type a case expression whose scrutinee is in weak head normal form with
This suggests the following rule:
\[
\TypeCaseWHNFIntermediate
\]
First, we assert this rule is only applicable to expressions in weak head
normal form. Second, we use the typing judgement for expressions in WHNF
previously introduced to determine the split of resources amongst the scrutinee
sub-expressions. Finally, we type all case alternatives with the same context, using the
$\vdash_{alt}$ judgement. 
%
Specifically:
\begin{itemize}
\item We introduce the case binder $z$ in the environment as a $\D$-bound
variable whose usage environment is the linear resources used to type the
scrutinee.
\item We make all the resources $\ov{\D_i}$ used to type the scrutinee available in the linear typing environment.
\item We annotate the \emph{alt} judgement with the disjoint set of linear resources $\ov{\D_i}$ used
to typecheck the scrutinee sub-expressions.
\item We annotate the judgement with the name of the case binder $z$ and use
the $\Mapsto$ arrow in the judgement -- this is of most importance when typing
the alternative itself, and will be motivated together with the alternative
judgement below.
\end{itemize}
%
Despite the key intuitions of typing a case expressions whose scrutinee is in
WHNF being conveyed by this rule, our treatment of such a case expression is
slightly more involved, as will be presented after discussing cases of
scrutinees not in WHNF.

The alternative judgement $\G;\D \vdash_{alt} \rho \to e :^z_\D \s \Rightarrow
\vp$ is used to type case alternatives, but it encompasses three
``sub-judgements``, distinguished by the arrow that is used:
for alternatives of case expressions whose scrutinee is in WHNF ($\Mapsto$),
for case expressions in which the scrutinee is not in WHNF ($\Rrightarrow$),
and for alternatives agnostic to the WHNF-ness of the scrutinee
($\Rightarrow$), with $\Rightarrow$ also generalizing the other two.
%
Following the $Case_\textrm{WHNF}$ rule in which we use the $\Mapsto$ alternative
judgement, the rule for typing a case alternative whose pattern is a
constructor with $n > 0$ linear components is:
\[
\TypeAltNWHNF
\]
The rule states that, for such a pattern matching a scrutinee already in
WHNF, we introduce the linear components of the pattern as $\D$-bound variables
whose usage environment matches the linear resources required to type the
corresponding constructor argument in the scrutinee, which comes annotated in
the judgement ($\ov{\D_i}$). Unrestricted fields of the constructor are
introduced as unrestricted variables. We note that the typing environment $\D$
always contains the resources $\ov{\D_i}$ in uses of the alternative
judgement.

Secondly, the rule for alternatives that match on the wildcard pattern:
\[
\TypeAltWild
\]
To type a wildcard alternative we simply type the expression with the main
judgement, ignoring all annotations on the judgement; recalling that the case
binder was already introduced in the environment with the appropriate usage
environment by the case expression, rather than in the case alternative rule.

Finally, consider an alternative matching on a case constructor without any
linear components. According to the definition of consuming a resource from
Linear Haskell, the linear resources of a scrutinee matching such a pattern are
fully consumed in the body of the corresponding alternative, since the
scrutinee must have been evaluated to a form that does not have any linear
components.
%
This definition agrees with the intuition we have developed by example in the
previous section, and with the typing rule we devised for alternatives matching
constructors without linear components.

% Indeed, matching on a constructor without
% linear arguments entails that all the scrutinee resources have been fully
% consumed, and thus are no longer available.

Taking into account that case expressions introduce the linear resources of the
scrutinee in the typing environment of all alternatives, and in the usage
environment of the case binder, we must reactively update the typing
environments after matching on such a pattern.
%
The $Alt0$ rule essentially encodes this insight, and is applicable regardless
of the WHNF-ness of the scrutinee (hence the $\Rightarrow$ arrow), as long as
the constructor pattern has no linear fields:
%
\[
\TypeAltZero
\]
The rule deletes the annotated scrutinee environment $\D_s$ from two select environments:
\begin{itemize}

\item The linear typing environment, effectively deleting the resources from
the scrutinee made available here by the case expressions (written
$\D[\cdot/\D_s]$, a substitution of the scrutinee typing environment by the
empty linear environment $\cdot$).

\item The usage environment of the case binder $z$, written $\G[\cdot/\D_s]_z$
to denote replacing the usage environment of the variable $z$ in $\G$, which
is necessarily $\D_s$ (since we always annotate the judgement with the
environment of the scrutinee), by the empty environment.

\end{itemize}
%
The rule faithfully encodes the notion that an expression matching such a
pattern is unrestricted when evaluated to WHNF, implying that all linear
resources have been consumed to produce it, and the result is something that
can be freely discarded or duplicated.
%
It ensures that when we match on an unrestricted pattern we no longer need to
consume the scrutinee resources. Otherwise, for example,
$\ccase{K_1~x}{\{K_2 \to K_2,K_1~y \to K_1~y\}}$ would not be well-typed since
the resource $x$ is not consumed in the first branch.
%
Furthermore, since the case binder in such an alternative refers to the
unrestricted expression, the case binder too may be used unrestrictedly, which
we allow by making its usage environment empty.

It might seem as though deleting the resources from the environment in this
rule is necessary to guarantee a resource is not used after it is consumed.
%
However, let us consider two discrete situations -- pattern matches in a case
expression whose scrutinee is in WHNF, and matches on a case expression whose
scrutinee is \emph{not} in WHNF:
%
\begin{enumerate}
\item When the scrutinee is in WHNF, it is either an unrestricted expression
against which any match will only introduce unrestricted variables, or an
expression that depends on linear resources. The first case trivially allows
any resource from the scrutinee in the alternatives as well. The second is
further divided:
\begin{enumerate}

\item The pattern is unrestricted while the
scrutinee is not, so entering this branch is impossible as long as the case
expression is well-typed; by contradiction, the linear resources from the
scrutinee could occur unrestrictedly in that branch, since from falsity
anything follows (\emph{ex falso quodlibet}).
%
For uniformity, we type such alternatives as those for scrutinees that are not in WHNF.

\item The pattern is linear and matches the scrutinee, in which case the
$AltN_{\textrm{WHNF}}$ is applicable instead of $Alt0$.

\item The pattern is linear but does not match the scrutinee and so, the same
reasoning as (1) above applies: any resource could theoretically be used in
such alternatives, however, for uniformity, it is also typed as though the
scrutinee were not in WHNF.

\end{enumerate}

\item However, if the scrutinee is not in WHNF, the resources occurring in the
scrutinee will be consumed when evaluation occurs. Therefore, the resources
used in the scrutinee cannot occur in the alternative body
(e.g. $x$ cannot occur in the alternative in $\ccase{close~x}{\{K_1 \to x\}}$)
-- regardless of the pattern.
%
% In fact, the resources from a scrutinee that is not in weak head normal form
% cannot occur in any of the alternatives, even ones matching on constructors
% with linear components, as the resources may have been consumed when evaluating
% the expression to weak head normal form.
%
We guarantee resources from a scrutinee that is not in weak head normal form
cannot occur/directly be used in any case alternative, in our rule for typing
cases not in WHNF, which we introduce below.

\end{enumerate}

% \todo[inline]{The trick here is to separate the case rules into two separate
% rules, one that fires when the scrutinee is in WHNF, the other when it isn't.}


\subsection{Proof irrelevant resources}

% \todo[inline]{O que é que eu vou fazer aqui? O que falta é conseguir tratar uma
% case expression de forma flexivel o suficiente. Explorar o scrutinee estar em
% WHNF ou não, agora é preciso usar essas ideias em typing rules.  Só preciso de
% dizer que para tipificar o caso em que não está em WHNF de forma rigorosa num
% sistema de tipos: Manter resources in scope pq é preciso consumir; Mas não
% podem ser usadas diretamente}

Resources used in a scrutinee that is not in weak head normal form must
definitely not be used in the case alternatives
% since they have been used in the evaluation of the scrutinee, as shown in
% the example above.
%
However, it is not sufficient to evaluate the scrutinee to weak head normal
form to \emph{fully} consume all resources used in the scrutinee, since
sub-expressions such as constructor arguments will be left unevaluated. To
\emph{fully} consume all resources occurring in the scrutinee, the scrutinee
must be evaluated either to \emph{normal form} or s.t. all linear components of
the scrutinee are fully evaluated, as witnessed by the $Alt0$ rule. In short,
for a case expression whose scrutinee is not in WHNF:
% We tackle this in due time, in the proof irrelevance section.
\begin{itemize}

\item The scrutinee resources must \emph{not} be used directly in the case alternatives;
\item But the result of evaluating the scrutinee to WHNF must still be
consumed, as all sub-expressions of the scrutinee remain unevaluated and must
be consumed.
\item Since the scrutinee resources cannot be consumed directly, they must be
consumed indirectly through $\D$-variables, namely, either the case binder, or
the linear pattern-bound variables introduced in the alternative.

\end{itemize}

% In alternatives of a case where the scrutinee is not in
% WHNF, we must also consume the result of evaluating the scrutinee to WHNF, but the
% scrutinee resources must definitely not be available for consumption. In
% practice, the result of evaluating the scrutinee must be consumed by using
% either the case binder or all the linear components of a constructor pattern,
% except for patterns matching an unrestricted pattern, which are handled with
% the $Alt0$ rule. For WHNF scrutinees, we encode mutual exclusivity between
% consuming resources directly, with the case binder, or through linear pattern
% variables, by introducing the latter two as $\D$-bound variables.  In essence,
% for the counterpart not-WHNF scrutinees, either the case binder or linear
% pattern-bound variables \emph{must} still be used to guarantee the evaluation
% result is consumed (thus their usage environment cannot be empty), but the
% scrutinee resources cannot be used directly.

We introduce \emph{proof irrelevant} resources, denoted as linear resources
within square brackets $[\D]$, to encode linear resources that cannot be
directly used (the $Var$ rule is not applicable). Proof irrelevant resources
are linear resources in all other senses, meaning they must be used
\emph{exactly once}. However, since proof irrelevant resources cannot be
forgotten neither used directly, they have to be consumed \emph{indirectly} --
by $\D$-bound variables.

To type a case expression whose scrutinee is in weak head normal form, we
type the scrutinee with linear resources $\D$ and type the case
alternatives by introducing the case binder with a usage environment $[\D]$,
having the same proof irrelevant linear context $[\D]$ in the typing
environment, annotating the judgement with the proof irrelevant resources,
and using the $\Rrightarrow$ judgement:
\[
\TypeCaseNotWHNF
\]
Note how the rule is quite similar to the one for scrutinees in WHNF, only
diverging in that the resources in the case binder, typing environment, and
judgement annotation, are made irrelevant.

% In practice, we can't know which resources are consumed by evaluating a given
% expression. The resources become in a limbo state -- they cannot be used
% directly because they might have been consumed, but they mustn't be considered
% as consumed, because they might not have been.  We say these resources enter a
% proof irrelevant state. They must still be tracked as though they weren't
% consumed, but they cannot be used directly to construct the program. How can we
% ensure these proof irrelevant resource variables are fully consumed? With usage
% environments -- for the case binder and for the pattern variables, and
% otherwise propagate

% \todo[inline]{The case binder and pattern variables will consume the scrutinee
% resources, be those irrelevant or relevant resources}

Finally, we recall the tentative $Case_\textrm{WHNF}$ rule presented before and
highlight its flaw: the $\G;\D \vdash_{alt} \rho \to e :^z_{\D_s} \s \Mapsto
\vp$ judgement is only well-defined for patterns $\rho$ matching the WHNF form
of the scrutinee, as the distribution of resources per constructor components
only makes sense for the constructor pattern matching the scrutinee.
Essentially, if the scrutinee is in WHNF the matching alternative is easily
determined, and must be treated with the specialized $\Mapsto$ judgement, which
only applies to the matching constructor.
%
Alternatives not matching the scrutinee, as mentioned in the discussion of the
$Alt0$ rule, could use resources arbitrarily as they will never be executed,
however, we uniformly treat non-matching alternatives as if the scrutinee were
not in WHNF. The rule for typing case alternatives whose scrutinee is in WHNF
is thus given by:
\[
\TypeCaseWHNF
\]
We note that it might seem unusual to specialize a rule for expressions in
WHNF, as programs scrutinizing an expression in WHNF are rarely written by a
developer. Yet, our system is designed to be suitable for optimising compilers
in which intermediate programs commonly scrutinize expressions in WHNF.
%
Foreshadowing, type preservation for the case-reduction substituting the case
binder and pattern variables in the alternative is not possible to prove
without branching on WHNF-ness, since otherwise the $\D$-substitution is not
well-defined.

\subsection{Splitting and tagging fragments}

Intuitively, in case alternatives whose scrutinee is not in weak head normal form,
% (and for scrutinees in WHNF which don't match the case alternative)
the proof-irrelevant resources introduced by the case expression must be fully
consumed, either via the case binder $z$, or by using all linear pattern-bound
variables (for uniformity, we also treat alternatives that do not match a
scrutinee in WHNF this way).

However, unlike with scrutinees in WHNF, the resources used by a
scrutinee not in WHNF do not necessarily match those used by each
sub-expression of the expression evaluated to WHNF.
%
Therefore, there is no direct mapping between the usage environments of the
linear pattern-bound variables and the resources used in the scrutinee.
% \todo{WAIT, there never was!
% Only when the K matches the scrutinee. Maybe we need a separate judgement for
% typing other constructors, which would be standalone and show up in this
% section too?}

We introduce \emph{tagged resources} to guarantee all linearly-bound pattern
variables are jointly used to consume all resources occurring in the
environment (in alternative to the case binder), or not at all. Given linear
resources $[\D_s]$ used to type a scrutinee, and a pattern
$K~\ov{x_\omega},\ov{y_i}$ with $i$ linear components, we assign a usage
environment $\D_i$ to each linear pattern variable where, $\D_i$ is obtained from the
scrutinee environment tagged with the constructor name and linear-variable
index $\lctag{\D_s}{K_i}$, and $\y[\D_i]$ is introduced in $\G$.
\[
\TypeAltNNotWHNF
\]
The tag consists of a constructor name $K$ and an index $i$ identifying the
position of the pattern variable among all bound variables in that pattern.
%
The key idea is that a linear resource $x$ can be split into $n$ resources at a
given constructor, where $n$ is the number of positional linear arguments of
the constructor.
%
This is given by the rule:
\[
\TypeVarSplit
\]
By assigning to each linear pattern variable a fragment of the scrutinee
resources with a tag, we guarantee that all linear pattern variables are
simultaneously used to consume all the scrutinee resources, since for any of
scrutinee resources to be used by a linear pattern-bound var be used, the
resources must be $Split$ for the fragments corresponding to that $\D$-var to
be consumed, and, consequently, the remaining fragments have to be consumed
through the other linear pattern-bound variables.
%
For instance, in $\lambda x.~\ccase{x}{z~\{K~a~b\to (a,b)\}}$, where $x$ is a
linear variable, the case alternatives are typed with $\irr{x}$ (proof
irrelevant $x$), $z$ is introduced as $\z[\irr{x}]$, and the pattern variables
are introduced as $\var[a][\lctag{\irr{x}}{K_1}]$ and
$\var[b][\lctag{\irr{x}}{K_2}]$, assuming both components of $K$ are linear.
%
We note how $Split$ can be applied both to relevant and proof irrelevant linear resources in $\D$.

% Using tags for fragments instead of fractions (e.g. $\D_s*i/n$) is necessary
% to guarantee we cannot use the same variable multiple times to consume
% multiple fractions of the resource. It also has the added benefit of allowing
% mixing of pattern variables bound at different alternatives (e.g.~$\lambda
% x~y.~\ccase{(x,y)}{(a,b)\to\ccase{(a,b)}{(z,w)\to(a,w)}}$).

%%%%% \section{Linear Core Examples}
%%%%% 
%%%%% \todo[inline]{If I have no time...}
%%%%% 
%%%%% Linear Mini-Core~\cite{cite:minicore} lists examples of Core programs where
%%%%% semantic linearity must be understood in order for them to be well-typed. In
%%%%% this section, we show those examples in Linear Core ($\lambda^\pi_\Delta$),
%%%%% briefly explaining why they are indeed well-typed.
%%%%% 
%%%%% \paragraph{Equations}
%%%%% 
%%%%% The Linear Haskell function is compiled in Linear Core as\\
%%%%% %
%%%%% \begin{minipage}{0.47\textwidth}
%%%%% \begin{code}
%%%%% data C = Red | Green | Blue
%%%%% f :: C ⊸ C ⊸ C
%%%%% f Red q = q
%%%%% f p Green = p
%%%%% f Blue q = q
%%%%% \end{code}
%%%%% \end{minipage}
%%%%% \begin{minipage}{0.47\textwidth}
%%%%% \[
%%%%% \begin{array}{ll}
%%%%% \lambda p{:}_1C~q{:}_1C.~\ccase{p}{p2{:}_{\{p\}}C \\
%%%%% \{Red \to q \\
%%%%% ; \_ \to \ccase{q}{q2{:}_{\{q\}}C\\
%%%%%   \{Green \to p2\\
%%%%%   ; \_ \to \ccase{p2}{p3{:}_{\{p\}}C \\
%%%%%   \{Blue \to q2\}} \}} \}}
%%%%% \end{array}
%%%%% \]
%%%%% \end{minipage}
%%%%% 
%%%%% \paragraph{Unrestricted Fields}
%%%%% 
%%%%% The following is well-typed:
%%%%% Let $\datatype{K}{K : A \lolli B \to C}$, and $f$:
%%%%% \[
%%%%% \lambda \xl.~\ccase{x}{\var[z][x]~\{ K~a~b \to (z, b) \}}
%%%%% \]
%%%%% 
%%%%% \paragraph{Wildcard}
%%%%% 
%%%%% The following is ill-typed:
%%%%% \begin{code}
%%%%% f = \x -> case x of z { _ -> True }
%%%%% \end{code}
%%%%% 
%%%%% \paragraph{Duplication}
%%%%% 
%%%%% The following is ill-typed:
%%%%% \begin{code}
%%%%% data Foo = Foo A
%%%%% f = \x -> case x of z { Foo a -> (z, a) }
%%%%% \end{code}


% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% {{{ Linear Core as a GHC Plugin
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\section{Linear Core as a GHC Plugin\label{sec:discuss:implementation}}

We have implemented the Linear Core type system as a plugin for the Glasgow
Haskell Compiler.
GHC plugins allow developers to inspect and modify programs being compiled by
GHC, at different stages of compilation~\cite{10.1145/3331545.3342599}.
%
In particular, for any given Haskell module, Core plugins run for (and receive
as input) every intermediate program produced in the compilation process, i.e.
from desugaring and after each optimising transformation.
%
This implementation further substantiates our claim that Linear Core is
suitable for the intermediate language of an optimising compiler.

The GHC Linear Core plugin~\cite{cite:linear-core-plugin} implements a
typechecker for Linear Core: given a Core program, our plugin typechecks the
linearity of all expressions bound in that program, failing if a linear
resource is not used \emph{exactly once} according to semantic linearity of the
$(\lambda^\pi_\Delta)$ system.
%
Most notably, the plugin successfully validates linearity throughout the
(optimising) compilation of linearity-heavy libraries, namely
\texttt{linear-base} and \texttt{linear-smc}, except in expressions whose
linearity depends on so-called \emph{multiplicity coercions}, which are an
avenue of future work ($\S$~\ref{sec:future-work}) exploring the intersection
of Linear Core with type equality coercions.
% Furthermore, the implementation accepts all example programs from Chapter~\ref{sec:linearity-semantically}
% deemed well-typed by Linear Core, which are marked with a
% \colorbox{notyet}{\notyetcolorname} background.

% Additionally, we discuss the implementation of the Linear Core type system
% directly in the Glasgow Haskell Compiler.

% This section discusses the implementation of Linear Core as a GHC Plugin, with
% a dash of painful history in the attempt of implementing Linear Core directly
% into GHC.

The implementation of Linear Core as a typechecker does not follow directly
from the description of the type system because Linear Core is not
\emph{syntax-directed}. Specifically, the most challenging features are
splitting linear resources amongst sub-derivations and consuming fragments of
resources through pattern-bound variables.
%
We use the following techniques to tackle the \emph{non-syntax-directedness} of
Linear Core, thus making the system more suitable to implement:
%
\begin{itemize}

\item Instead of non-deterministically splitting linear resources amongst
sub-derivations, we thread input/output linear resources through each
derivation using the resource management for linear logic described
by~\cite{DBLP:journals/tcs/CervesatoHP00}.
% \todo{Escrever uma regra?}

% In a case expression whose scrutinee is not in WHNF,
\item Pattern variables bound in a case alternative, for a scrutinee not in WHNF,
are introduced as $\D$-variables with usage environment $\lctag{\irr{\D}}{K_i}$,
where $\D$ are the scrutinee resources and $K_i$ the tag of that pattern
variable. To use the resources through the pattern-bound $\D$-vars, they must
be first $Split$ into fragments.

We consume tagged fragments of a resource \emph{as needed}, i.e., when a resource,
whose usage environment has a fragmented resource with tag $K_j$, is used, we $Split$
the matching resource according to the constructor $K$ and consume the fragment
$K_j$, rather than eagerly determining which resources need to be fragmented to
do so.
%
We note that it is safe to destructively fragment the resource, i.e. removing
the whole resource and only leaving the split fragments, because resources are
only $Split$ when a fragment is needed and, consequently, if a fragment is
consumed, using the ``whole'' resource as well violates linearity.

\end{itemize}
%
Furthermore, our implementation must infer the usage environments of binders in
a recursive let group before using them to typecheck the let body. We use a
naive $O(n^2)$ algorithm (where $n$ is the number of let bindings) to determine
these usage environments, but discuss an avenue of further research regarding
this inference challenge in Section~\ref{sec:future-work}.

The usage environments of a recursive group of binders (that is not necessarily
strongly-connected) is computed in two separate passes.
%
First, we calculate a \emph{naive environment} by recording the linear
resources semantically used in the binder bodies, while counting \emph{uses}
(not syntactic occurrences) of the mutually recursive let variables.
%
Second, the binder names and corresponding \emph{naive environment} (mapping
each linear resource to $1$ and the recursive variables to the $n$ number of
times they are \emph{used}) in Cartesian pairs are given as input to
Algorithm~\ref{computeRecUsages}, which computes the actual usage environment
of each binder.
%
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
%
Intuitively, the algorithm, for each recursive binder, iterates over the
(initially naive) usage environments and substitutes occurrences of the
recursive binders by their corresponding usage environment,
scaled up by the amount of times that recursive binder is used in the
environment being updated. The result is the least upper bound of linear
resources used by each strongly-connected group of mutually recursive bindings
(for each binder of such a group), since all occurrences of the recursive
binders in the usage environments will be substituted away by the corresponding
recursive usage environments.
%
% The high-level description is:
% \begin{itemize}
%     \item Given a list of binders and their naive environment ($(f, F), (g, G),
%     (h, H)$) in which each use of $f, g, h$ is mapped to a count $n$ in $F, G, H$
%
%     \item For each pair of a letrec-bound variable and corresponding usage
%     environment, update all bindings and their usage as described in the
%     algorithm
%
%     \item After iterating through all bound rec vars, all usage environments
%         will be free of recursive bind usages, and hence describe the ``final'' usage environment
% \end{itemize}
%
The complexity of computing a usage environment for $n$ recursive let binders
is quadratic in $n$,
% i.e. the algorithm has $O(n^2)$ complexity,
but this is not an issue since it is uncommon to have more than a handful of
binders in the same recursive let block.

The results of running the Linear Core GHC plugin on large established
libraries focused around linear types are given by
Figure~\ref{fig:core-plugin-res}.
%
We compiled the libraries \texttt{linear-smc}, a library presented in the
work~\cite{10.1145/3471874.3472980} (1500 lines), \texttt{linear-base} (4000
lines), the Haskell standard library for programming with linear types,
comprised of over 100 modules, and
\texttt{priority-sesh}~\cite{10.1145/3471874.3472979} (1400 lines), a
session-types library, using our plugin.
%
We count the number of programs accepted by our implementation, where each
top-level binding in a module counts as a program, and every such binding is
typechecked once per optimisation pass. i.e., we typecheck all intermediate
programs produced by GHC. The total amount of programs rejected by the
typechecker are given in the ``Total Rejected'' column, but we distil these
rejections into ``Unique Rejections'' by removing duplicate rejections (those
of the same program and for the same linearity-violating reason, but occurring
at different stages). We further categorize the unique rejections into ``Linear
modulo Call-by-name'', ``Linear Rejected'', ``Not Linear Rejected'', and
``Unknown Rejected''.
%
Using the plugin, \texttt{linear-base} takes 35 seconds to compile, instead of
20 seconds. We note, however, that the implementation is not performance
conscious, and types every intermediate program from scratch, instead of
maintaining linearity information throughout the pipeline.

Programs ``linear modulo call-by-name'' are a class of programs
which scrutinize a variable, but then uses the variable in the case
alternatives of the case scrutinizing it. As will be made clear in
Section~\ref{sec:reverse-binder-swap-considered-harmful}, these programs can be
understood as linear as long as applications of linear functions binding these
variables are \emph{not} reduced \emph{call-by-name}, because, in doing so,
linear resources are duplicated. In Core, these programs are not seen as
linear, and thus GHC does not not reduce them using a call-by-name evaluation strategy.
% We have a flag in our implementation to accept some of these programs...
%
``Linear Rejected'' programs include different kinds of programs which are
rejected by the Linear Core system, but are still semantically linear. An
example is a program to which a rewrite rule was applied, resulting in an
application of unrestricted function to a linear resource in the first argument
to |build|:
\begin{code}
take :: Int -> Replicator a ⊸ [a]
take = \ (ds :: Int) (r :: Replicator b) ->
     case ds of
       1 -> build (\(c :: b -> a -> a) (n :: a) -> c (extract r) n)
       ...
\end{code}
We know the linear resource is still used linearly because |build| will
always instance the unrestricted function to $(:)$ (read \emph{Cons}), which is
linear. Additionally, these include programs scrutinizing a value of a type of
which all constructors have no linear components, but only matching on the
default alternative, programs where common-sub-expression elimination
substituted more than one occurrence of |Ur x| by |y|, in the body of
scrutinizing |y| (a linear variable), and other programs affected by rewrite rules.
%
``Not Linear Rejected'' indicate programs that we do not understand as linear,
semantically, and are simultaneously rejected by Linear Core and its
implementation. An example, where the last component of |HashMap|, |wwz|,
is linear, but is not being consumed in the case alternative matching on it:
\begin{code}
jssvi :: Ur Bool ⊸ Set Int ⊸ Ur (TestT IO ())
jssvi (a :: Ur Bool) (b :: Set Int)
  = case a of
    Ur ss -> case b  of
      HashMap wwx wwy wwz ->
        jump wjssAd ss
\end{code}
%
Finally, ``Unknown Rejected'' programs are those whose validity we did not
check. These include both programs accepted by Linear Core, but not by its
implementation, and programs that are simply rejected by Linear Core, but which
were not categorized.

\input{prototype/core-plugin-results}

The results indicate our mostly direct implementation of Linear Core is
successful in accepting the vast majority of the thousands of intermediate
programs produced by GHC when compiling libraries that make extensive use of
linear types.
%
The programs rejected by the Linear Core plugin, in \texttt{linear-base},
besides validating that our implementation is faithful to the
$\lambda^\pi_\Delta$ system of insofar as programs that should not be accepted
are deemed ill-typed, provide further insight into the remaining
details required to fully typecheck linearity in a mature optimising compiler.


% Talk about using our plugin on linear-base and other code bases... If I can get
% a few more case studies it would be pretty good. But then it's imperative to
% also use -dlinear-lint and make sure my plugin rejects a few of the examples

%%% \subsection{Consuming tagged resources as needed}
%%% 
%%% As discussed in Section~\ref{}, pattern-bound linear variables are
%%% put in the context with a \emph{tagged} usage environment with the resources of
%%% the scrutinee. In a \emph{tagged} usage environment environment, all resources
%%% are tagged with a constructor and an index into the many fields of the
%%% constructor.
%%% 
%%% In practice, a resource might have more than one tag. For example, in the following
%%% program, after the first pattern match, |a| and |b| have, respectively, usage
%%% environments $\{\lctag{x}{K_1}\}$ and $\{\lctag{x}{K_2}\}$:
%%% \begin{code}
%%% f x = case x of
%%%        K a b -> case a of
%%%         Pair n p -> (n,p)
%%% \end{code}
%%% However, in the following alternative, |n| has usage environment
%%% $\{\lctag{\lctag{x}{K_1}}{Pair_1}\}$ and |p| has
%%% $\{\lctag{\lctag{x}{K_1}}{Pair_2}\}$. To typecheck
%%% |(n,p)|, one has to $Split$ |x| first on |K| and then on |Pair|, in order for
%%% the usage environments to match.
%%% 
%%% In our implementation, we split resources on demand (and don't directly allow
%%% splitting linear resources), i.e. when we use a tagged resource we split the
%%% linear resource in the linear environment (if available), but never split otherwise.
%%% %
%%% Namely, starting on the innermost tag (the closest to the variable name), we
%%% substitute the linear resource for its split fragments, and then we iteratively
%%% further split those fragments if there are additional tags.
%%% %
%%% We note that it is safe to destructively split the resource (i.e. removing the
%%% original and only leaving the split fragments) because we only split resources
%%% when we need to consume a fragment, and as soon as one fragment is consumed
%%% then using the original ``whole'' variable would violate linearity.
%%% 
%%% In the example, if |n| is used, we have to use its usage environment, which in
%%% turn entails using $\lctag{\lctag{x}{K_1}}{Pair_1}$, which has two tags. In this order, we:
%%% \begin{itemize}
%%% \item Split $x$ into $\lctag{x}{K_1}$ and $\lctag{x}{K_2}$
%%% \item Split $\lctag{x}{K_1}$ and $\lctag{x}{K_2}$ into
%%%   \begin{itemize}
%%%   \item $\lctag{\lctag{x}{K_1}}{Pair_1}$ and $\lctag{\lctag{x}{K_1}}{Pair_2}$
%%%   \item Leave $\lctag{x}{K_2}$ untouched, as we only split on demand, and we aren't using a fragment of $\lctag{x}{K_2}$.
%%%   \end{itemize}
%%% \item Consume $\lctag{\lctag{x}{K_1}}{Pair_1}$, the usage environment of $n$, by removing it from the typing environment.
%%% \end{itemize}

%%%\subsection{Merging Linear Core into GHC\label{sec:merging-linear-core}}
%%%
%%%Describe the ticket for linear Core, the pending MRs, and the difficulty in
%%%even annotating the bind site across optimisations regardless of multiplicities.

% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% {{{ Metatheory
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Metatheory\label{sec:main:metatheory}}

The $\lambda^\pi_\D$ system is sound: well-typed programs in Linear Core do not
get \emph{stuck}. Besides type safety ($\S$~\ref{sec:type-safety-meta}), we
prove multiple optimising transformations preserve linearity
($\S$~\ref{sec:optimisations-preserve-types-meta}), and prove an auxiliary
result regarding proof irrelevant resources, stating that a case alternative
well-typed in a proof irrelevant context is also well-typed if proof irrelevant
resources are substituted by an arbitrary environment of relevant resources.
%
Additionally, we state our assumptions that outline an isomorphism between
using a linear variable $\xl$ and a $\D$-variable $\xD$ that consumes existing
resources $\D$, for any $\D$.

\section{Assumptions}

We use two main assumptions in our proofs, which are dual.
%
First, a program well-typed with a linear variable ($\xl$) is equivalently
well-typed if that same linear variable were instead $\D$-bound ($\xD$) with
usage environment $\D$, $\D$ were available in the linear context instead of
the linear variable.
% , and occurrences of $x$ were substituted by $\D$ in the
% usage environments of other $\D$-vars in $\G$.
%
% First, we state that a linear variable $\xl$ can be replaced by a $\D$-bound
% variable as long as the context
%
\LinearDeltaRelationLemma
%
\noindent Second, a program well-typed with resources $\D$ and $\D$-bound
variable ($\xD$) is equivalently well-typed, as long as $\D$ is consumed
through the use of $x$, if $x$ is moved to the linear context, resources $\D$
are removed from the linear context, and occurrences of $\D$ whole in usage
environments are substituted by $x$ (occurrences of fragments of $\D$ in usage
environments are unimportant since $\D$ was consumed whole by $x$, not by any
of the fragment-using $\D$-vars).

\DeltaLinearRelationLemma

% Intuitively, a linear variable 

We additionally state that unrestricted resources are equivalent to $\D$-bound
variables with an empty ($\cdot$) usage environment:

\DeltaUnrestrictedRelationLemma

\section{Irrelevance}

As discussed above, proof irrelevant resources are resources that can only be
consumed indirectly, and are used to type case expressions whose scrutinee is
not in WHNF, essentially encoding that the scrutinee resources must be consumed
through the case binder or the linear pattern-bound variables.
%
As a case expression is evaluated, the scrutinee will eventually be in WHNF,
which must then be typed with rule $Case_{\textrm{WHNF}}$.
%
Crucially, these rules must ``work together'' in the system, in the sense that
case expressions typed using the $Case_{\textrm{Not WHNF}}$ rule must also be
well-typed after the scrutinee is evaluated to WHNF, which is then typed using
the $Case_{\textrm{WHNF}}$ rule.

% The type preservation theorem states that a well-typed expression
% remains well-typed in the presence of evaluation. Specifically, when the case
% expression whose scrutinee is evaluated to WHNF is handled in the
% preservation proof.

The \emph{Irrelevance} lemma is required to prove preservation for that
evaluation case. We need to prove that the alternatives of a case expression
typed with proof irrelevant resources are still well-typed when the proof
irrelevant resource is substituted by the scrutinee resources as it is evaluated to WHNF.
In this sense, the \emph{Irrelevance} lemma witnesses the soundness of typing a
case alternative with proof irrelevant resources in a certain context with respect to
typing the same expression with arbitrary resources (we note, however, typing
an alternative with proof irrelevant resources is not complete wrt using
arbitrary resources -- a counter example needs only to use a resource
directly).

\WHNFConvSoundness

\noindent Intuitively, the lemma holds since proof irrelevant resources can
only be used through the case binder or pattern-bound variables. If we
consistently replace the proof irrelevant resources both in the typing
environment and in the usage environments containing them, the expression
remains well-typed. We note that the proof irrelevant resources are always
unique when introduced in such a case alternative (we always take the scrutinee
environment to make irrelevant, and allow nested ``irrelevantness''), so the
case binder has the only occurrence of those resources in the $\G$ environment.
% (being somewhat akin to congruence).
%
The proof is given in Section~\ref{sec:proof:irrelevance}.

\section{Type safety\label{sec:type-safety-meta}}

We prove type safety of the Linear Core system via the standard type
preservation and progress results. As is customary, we make use of multiple
substitution lemmas, one for each kind of variable: unrestricted variables
$\xo$, linear variables $\xl$, and $\D$-bound variables $\xD$.

% We start with the auxiliary results, as we will make use of them in a select part of the preservation proof.

\TypePreservationTheorem
%
\noindent Type preservation states that a well-typed expression $e$ that
evaluates to $e'$ remains well-typed under the same context:
%
The proof ($\S$~\ref{sec:proof:type-preservation}) is done by structural induction on the reductions $e \longrightarrow
e'$ from the operational semantics. Most cases are straightforward and usually
appeal to one or more of the substitution lemmas described below. The most
interesting case is that of case expressions whose scrutinee can be further
evaluated -- we branch on whether the scrutinee becomes in WHNF, and invoke the
\emph{Irrelevance} lemma if so.
%
This case guarantees that the separation of rules for treating scrutinees is
consistent, in the sense that a well-typed case expression with a scrutinee not
in WHNF remains well-typed after the scrutinee is evaluated to WHNF.

\ProgressTheorem
%
\noindent Progress states that the evaluation of a well-typed term does not block:
Similarly, progress is proved by induction on typing ($\S$~\ref{sec:proof:progress}).

\subsection{Substitution Lemmas}

The preservation and progress theorems depend on multiple substitution lemmas,
one for each kind of variable, as is standard.
% The proofs are given in Section~\ref{sec:proof:substitution-lemmas}.
% The ... themselves diverge from their common formulation, because
% $\D$-variables refer to linearly bound variables, so substitution must take into account


The linear substitution lemma states that a well-typed expression $e$ with a
linear variable $x$ of type $\s$ remains well-typed if
occurrences of $x$ in the $e$ are replaced by an expression $e'$ of the same
type $\s$, and occurrences of $x$ in the linear context and in usage
environments of $\D$-bound variables are replaced by the linear context $\D'$
used to type $e'$:

\LinearSubstitutionLemma

\noindent Where $\G[\D'/x]$ substitutes all occurrences of $x$ in the usage
environments of $\D$-variables in $\G$ by the linear variables in $\D'$.
% ($x$ couldn't appear anywhere besides usage environments of $\D$-bound variables, since $x$ is linear).

The substitution of the resource in the usage environments is illustrated
by the following example. Consider the term $\llet{y = use~x}{y}$ where $use$ and $x$ are free variables:
if we replace occurrences of $x$ by $e'$ (where $\G;\D \vdash e : \s$), then the
``real'' usage environment of $y$ goes from $\{x\}$ to $\D$. If we don't update
the usage environment of $y$ accordingly, we'll ultimately be typing
$y{:}_{\{x\}}\vp$ with $\D$ instead of $x$, which is not valid.

The linear substitution lemma extends to case alternatives as well.
The lemma for substitution of linear variables in case alternatives is similar
to the linear substitution lemma, applied to the case alternative judgement.
% Is slightly more involved, in the sense that there are more environments in which the
% substitution $[\D/x]$ must be applied (for the same reason):
%
\LinearSubstitutionAltsLemma
%
\noindent We further require that the environment annotated in the case
alternative judgement, $\D_s$, is a subset of the environment used to type the
whole alternative $\D_s \subseteq \D$. In all occurrences of the alternative
judgement (in $Case_{\textrm{WHNF}}$ and $Case_{\textrm{Not WHNF}}$), the
environment annotating the alternative judgement is \emph{always} a subset of
the alternative environment.

The substitution lemma for unrestricted variables follows the usual
formulation, with the added restriction (common to linear type systems) that
the expression $e'$ that is going to substitute the unrestricted variable $x$
is typed on an empty linear environment:
%
\UnrestrictedSubstitutionLemma
%
\noindent Similarly, we also prove the substitution of unrestricted variables preserves types on an alternative case expression:
%
\UnrestrictedSubstitutionAltsLemma

Finally, we introduce the lemma stating that substitution of $\D$-bound
variables by expressions of the same type preserves the type of the original
expression.
%
What distinguishes this lemma from traditional substitution lemmas is that the
usage environment $\D$ of the variable $x$ being substituted by expression $e'$
must match exactly the typing environment $\D$ of $e'$ and the
environment of the original expression doesn't change with the substitution:
%
\DeltaSubstitutionLemma
%
\noindent Intuitively, if $x$ is well-typed with $\D$ in $e$, substituting $x$
by an expression $e'$ which is typed in the same environment $\D$ allows the
distribution of resources $\D,\D'$ used to type $e$ across sub-derivations to remain
unchanged. To prove the theorems, we don't need a ``stronger'' substitution of
$\D$-vars lemma (allowing arbitrary resources $\D''$ to type $e'$, as in other
substitution lemmas), as we only ever substitute $\D$-variables by expressions
whose typing environment matches the variables usage environment. However, it
is not obvious whether such a lemma is possible to prove for $\D$-variables,
even if the resulting environment were modified, because they $\D$-variables are
not necessarily used.
% (e.g. let $\G;\D \vdash e :\s$ and $\G; \D' \vdash \llet{x = e'}{x}$, if we
% substitute $e$ for $x$ the resources $\D'$ are no longer consumed).

The $\D$-substitution lemma on case alternatives reflects again that the typing
environment of the expression substitution the variable must match its usage
environment. We recall that $\D_s \subseteq \D,\D'$ states that the annotated
environment is always contained in the typing environment, which is true of all
occurrences of this judgement. An alternative formulation of this lemma could
instead explicitly list $\D_s$ as part of the typing environment for the same
effect:

\DeltaSubstitutionAltsLemma

The proofs for substitution lemmas of linear, unrestricted, and
$\D$-variables are available in Section~\ref{sec:proof:substitution-lemmas}.

%TODO! Substitution of proof-irrelevant linear variables preserves typing. The
%term always remains the same because $x$ cannot occur in any term, however, all
%variables that refer to $x$ in their usage environment must now refer the usage env. of the substitee (e.g. $[x] => [\D]$).
%This seems trivial to see correct, since all occurrences are in environments, so we get some equivalence similar to the one we need for the proof of Alt0.
%
%TODO: Multiplicity substitution preserves typing lemma
%
%TODO: Canonical forms lemma
%
%TODO: Corollary of $\Delta$-var subst. for $\ov{\Delta}$
%
%TODO: Constructor app typing:
%If $\Gamma, \Delta \vdash K~\ov{e}$ and $K{:}\ov{\sigma\to\pi}~T~\ov{p} \in \Gamma$ and $\hasnolinearvars{\Gamma}$
%then $\ov{\Gamma, \Delta_i \vdash e_i : \sigma_i}$

\section{Optimisations preserve linearity\label{sec:optimisations-preserve-types-meta}}

One of the primary goals of the Linear Core type system is being suitable for
intermediate representations of optimising compilers for lazy languages with
linear types. In light of this goal, we prove that \emph{multiple optimising
transformations} are type preserving in Linear Core, and thus preserve linearity.

The optimising transformations proved sound wrt Linear Core in this section
have been previously explained and motivated in
Section~\ref{sec:core-to-core-transformations}.
%
Transformations are described by an arbitrary well-typed expression with a certain shape, on
the left hand side (lhs) of the arrow $\Longrightarrow$, resulting in an expression on
the right hand side (rhs) that we prove to be well-typed.
%
% For our proofs, we assume the lhs to be a well-typed expression and prove the
% rhs is well-typed as well.
%
For each transformation, we describe the intuition behind the transformation
preserving linearity in our system.

\subsection{Inlining}

% To the best of our knowledge, there is no linear type system for which inlining
% preserves linearity\footnote{https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0111-linear-types.rst\#id90}

\input{language-v4/proofs/optimizations/Inlining}

\subsection{\texorpdfstring{$\beta$}{Beta}-reduction}

\input{language-v4/proofs/optimizations/BetaReduction}

\subsection{Case of known constructor}

\input{language-v4/proofs/optimizations/CaseOfKnownConstructor}

\subsection{Let floating}

\input{language-v4/proofs/optimizations/LetFloating}

\subsection{\texorpdfstring{$\eta$}{Eta}-conversions}

\input{language-v4/proofs/optimizations/EtaConvs}

\subsection{Binder Swap}

The binder swap transformation applies to case expressions whose scrutinee is a
single variable $x$, and it substitutes occurrences of $x$ in the case
alternatives for the case binder $z$. If $x$ is a linear resource, $x$ cannot
occur in the case alternatives (as we conservatively consider variables are not
in WHNF), so the substitution preserves types vacuously. Otherwise, $x$ can be
freely substituted by $z$, since $z$ is also an unrestricted resource (it's
usage environment is empty because $x$ is unrestricted).

\input{language-v4/proofs/optimizations/BinderSwap}

\subsection{Reverse Binder Swap Considered Harmful\label{sec:reverse-binder-swap-considered-harmful}}

The reverse binder swap transformation substitutes occurrences of the case
binder $z$ in case alternatives by the scrutinee, when the scrutinee is a
variable $x$.

\ReverseBinderSwapTheorem

\noindent This is exactly reverse from what the binder swap transformation
does in hope of eliminating multiple uses of $x$ so as to inline it. However, by
using the scrutinee $x$ instead of the case binder, we might be able to float
out expressions from the alternative using the case binder. For example, we
might float an expensive computation involving $z$ out of the case alternative,
where $z$ is out of scope but $x$ isn't:
\[
\begin{array}{l}
\lambda x.~\lletrec{go~y = \ccase{x}{z~\{(a,b) \to \dots (expensive~z) \dots\} }}{\dots}\\
\Longrightarrow_\textrm{Reverse binder swap}\\
\lambda x.~\lletrec{go~y = \ccase{x}{z~\{(a,b) \to \dots (expensive~x) \dots\} }}{\dots}\\
\Longrightarrow_\textrm{Float out}\\
\lambda x.~\llet{t = expensive~x}{\lletrec{go~y = \ccase{x}{z~\{(a,b) \to \dots t \dots\} }}{\dots}}\\
\end{array}
\]
If $go$ is a loop, by applying the reverse binder swap we now only compute
$expensive~x$ once instead of in every loop iteration.

Despite GHC applying the reverse binder swap transformation to core programs
during Core-to-Core optimisation passes, this optimisation violates linearity
when considered as a transformation on Linear Core programs. In practice, the
optimisation preserves linearity in Core when applied as part of the GHC
transformation pipeline only due to the occurrence analyser being naive with
regard to semantic linearity. Initially, it might seem as though an expression
in which a variable $x$ occurs both in the case scrutinee and in the
alternatives is linear, for example:
\[
\G; \xl \vdash \ccase{x}{\_ \to x} : \s
\]
The reasoning is done by branching on whether $x$ refers to an expression in
WHNF or an unevaluated thunk.
\begin{itemize}
\item If $x$ refers to an unevaluated expression, then scrutinizing it results
in the expression bound by $x$ to be evaluated to WHNF. In a subsequent use of
$x$ in the alternatives, $x$ refers to the evaluated scrutinee in WHNF, which
must be consumed. Since $x$ is just another name (like the case binder) for the
scrutinee in WHNF, we may use it instead of the case binder or pattern
variables.
\item If $x$ already refers to an expression evaluated to WHNF, then
scrutinizing it in a case expression is a no-op, thus we may use it again (in
mutual exclusion with the case binder and pattern variables)
\end{itemize}
%
% This idea would be encoded by a possible rule like $$\TypeCaseVar$$
%
Even though, on its own, it makes intuitive sense that this example indeed uses
$x$ linearly, when considered as part of a complete type system, allowing this
expression to be linear makes the system unsound.

We recall that $\beta$-reduction reduces an application of a linear function
using call-by-name -- if we know the argument is used exactly once, a binding
to share the result of computing the argument is unnecessary, so we instead
substitute the argument expression for the linearly-bound variable in the
$\lambda$-body directly.

Consider the function application $$(\lambda x.~\ccase{x}{\_ \to x})~(use~y)$$
where $y$ is a free linear variable. Assuming $\lambda x.~\ccase{x}{\_ \to x}$
is a linear function by the reasoning above, $\beta$-reduction transforms the
application in $(\ccase{x}{\_ \to x})[use~y/x]$, i.e. $\ccase{use~y}{\_ \to
use~y}$. Now, $y$ is a linear variable \emph{consumed} in the scrutinee of the case
expression, yet it occurs in the body of the case alternative as well --
linearity is violated by using the linear resource $y$ twice.

Essentially, Linear Core would be unsound, and even duplicate resources, if the
above kind of expressions, where linear variable scrutinees occur in the
alternatives body, were well-typed, because of its interaction with the
call-by-name reduction of linear functions. In this sense, the reverse binder
swap is an optimisation that creates ill-typed expressions from well-typed
ones, so it is deemed an invalid optimisation that doesn't preserve types in
our system.

The reverse binder swap is not a problem in the GHC simplifier because of the
weaker notion of linearity understood by occurrence analysis. Occurrence
analysis is a static analysis pass which can be used to determine whether a
lambda application can be $\beta$-reduced call-by-name, and $\ccase{x}{\_ \to
x}$ is \emph{not} seen as using $x$ linearly by the analysis. Thus,
$\beta$-reduction is done with call-by-need on such an expression. If the above
example were reduced with call-by-need:
\[
\begin{array}{l}
(\lambda x.~\ccase{x}{\_ \to x})~(use~y)\\
\Longrightarrow_\textrm{call-by-need $\beta$-reduction}\\
\llet{x = use~y}{\ccase{y}{\_ \to y}}
\end{array}
\]
Then the computation using $y$ would be let-bound, and $y$ used as a scrutinee
variable, which is indeed an expression semantically linear in $x$.

Concluding, in being able to understand more programs as linear, our type
system allows more expressions to be considered linear for $\beta$-reduction
without a let-allocation, however, it makes reverse binder swap an invalid
transformation since its output, when considered linear, might violate
linearity when further optimised.

% (Link to ticket)
% 
% \begin{tabbing}
% (1) All optimisations preserve (semantic) linearity\\
% (2) If a function is (semantically) linear, then we can evaluate it using call-by-name and preserve linearity\\
% (3) Reverse binder swap is an optimisation\\
% (4) If reverse binder swap is applied to a case scrutinizing a linear resource in the body (`e`) of a linear function `f`, then the function is still linear by (1)\\
% (5) If we evaluate `f`, we do it call-by-name because of (2)\\
% (6) Call-by-name substitution of the linear argument in the body of a function has been reverse binder swapped doesn’t preserve linearity\\
% (7) Contradiction: By 3 and 1, `f` is linear after reverse-binder-swap. By 2, we can substitute arguments to `f` call-by-name and preserve linearity, which contradicts with 6 that says call-by-name substitution after reverse binder swap violates linearity\\
% \end{tabbing}

% Conclusion:
% Either we need to forfeit that we can always substitute call-by-name linear
% function applications, or we forfeit that reverse binder swap preserves
% linearity (instead, it preserves a weaker notion of linearity understood by the
% syntatic-occurrence-analyzer)

% \todo[inline]{Reverse-binder-swap is only well-defined in certain scenarios
% where the optimizations don't apply call-by-name beta-reduction after the
% reverse-binder-swap optimization -- otherwise we would duplicate resources.
% In this case, it is not a matter of syntatic vs semantic linearity
% }

% \todo[inline]{
% Mention, from ``Call-by-name, call-by-value, call-by-need and the linear lambda calculus'':
% The call-by-name calculus is not entirely suitable for reasoning about
% functional programs in lazy languages, because the beta rule may copy the
% argument of a function any number of times. The call-by-need calculus uses a
% diferent notion of reduction, observationally equivalent to the call-by-name
% calculus. But call-by-need, like call-by-value, guarantees that the argument
% to a function is not copied before it is reduced to a value.
% }

% It's also interesting to note that reverse-binder-swap preserves linearity under pure call-by-need but not under call-by-name, because
% (In the sense that if EVEN linear functions reduce call-by-need rather than call-by-name, then it would preserve optimisations)

% Reduce call-by-name linear function application
% \begin{code}
% f y = (\x. case x of _ -> x:1) (h y)
% ===>
% f y = (case x of _ -> x)[h y/x]
% ===>
% f y = (case h y of _ -> h y) -- consume y twice.
% \end{code}
% 
% Vs. call-by-need
% \begin{code}
%  (\y = (\x. case x of _ -> x:1) (h y)) e
% ===>
%     let y = e in
%        let x = h y in
%         case x of _ -> x
% ===>
%        let x = h e_v in
%         case x of _ -> x
% ===>
%         case x_v of _ -> x_v
% \end{code}

\subsection{Case of Case}

The case of case transformation applies to case expressions whose scrutinee is
another case expression, and returns the innermost case expression transformed by repeating
the outermost case expression in each alternative of the innermost case,
scrutinizing the original alternative body.

Intuitively, since the scrutinee of the outermost case is not in WHNF, no
resources from it can directly occur in the outermost alternatives. By moving
the outermost alternatives inwards with a different scrutinee, the alternatives
remain well-typed because they are typed using either the case binder or the
pattern bound variables, which, by the \emph{Irrelevance} lemma, makes it
well-typed for any scrutinee consuming arbitrary resources. The proof is given in Section~\ref{sec:proof:caseofcase}.

\CaseOfCaseTheorem

% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% vim: fen fdm=marker
