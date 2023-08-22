%include polycode.fmt
%format ⊸ = "\lolli"

% Needed bc of renewcommand in orders...
% \input{proof}
% \input{language-v2/proof}
% \input{language-v3/proof}
% % Proof macros for v4
% \input{language-v4/proof}

\chapter{Linear Core}

\todo[inline]{This is the Introduction. We should start elsewhere}

\todo[inline]{
    Inicío deve motivar o leitor, e temos de explicar qual é o problema da
    linearidade sintatica em Haskell (vs semantica), e a interação disso com o
    call-by-need/lazy evaluation. Quase como se fosse um paper.
}

\todo[inline]{Syntatic vs semantic linearity. Various examples}

\todo[inline]{Interação de linearity com a call-by-need/laziness}

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

\todo[inline]{This was the old introduction to chapter 3. I think we can do better}

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
languages in its pipeline: Haskell and its main intermediate language, Core
%
(Core is a much smaller language than the whole of Haskell, even though we can
compile the whole of Haskell to Core).
%
The addition of linear types to
GHC Haskell required changing the type system of both languages. However,
Linear Haskell only describes an extension to the surface-level Haskell type
system, not Core. Nonetheless, in practice, Core is linearity-aware.

We want Core and its type system to give us guarantees about desugaring and
optimizing transformations with regard to linearity just as Core does for types
-- a linearly typed Core ensures that linearly-typed programs remain correct
both after desugaring and across all GHC optimizing transformations,
i.e.~linearity is preserved when desugaring and optimisations should not
destroy linearity.

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


Core is already annotated with linearity, but its type-checker \textbf{currently ignores linearity annotations}.
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

\todo[inline]{Expand a bit on call-by-need vs call-by-value linearity. How can
we make this a bigger part of our work and introduction?}

Consider the example in Figure~\ref{fig:first-motivation}, an expression in which
$y$ and $z$ are variables bound by a $\lambda$-abstraction, and both are
annotated with a multiplicity of \texttt{1}. Note that let-binding $x$ doesn't
necessarily consume $y$ and $z$ because of Core's call-by-need semantics.
%
\begin{figure}[h]
  \begin{minipage}[l]{0.49\textwidth}
    \begin{code}
    let x = (y, z) in
    case e of
      Pat1 -> … x …
      Pat2 -> … y … z …
    \end{code}
  \end{minipage}
  \begin{minipage}[r]{0.49\textwidth}
    \caption{Example Inlining}
  \end{minipage}
\label{fig:first-motivation}
\end{figure}
%
In the example, it might not seem as though $y$ and $z$ are both being
consumed linearly but, in fact, they both are. Given that in the first branch
we use $x$ -- which entails using $y$ and $z$ linearly -- and in the second
branch we use $y$ and $z$ directly, in both branches we are consuming both $y$
and $z$ linearly.

% TODO:HELP: Fix links to motivation-2 showing up as links to motivation-1
Similarly, consider the program in Figure~\ref{fig:second-motivation} with a
let-binding that uses $x$, a linearly bound $\lambda$-variable. In surface
level Haskell, let-bindings always consume linear variables \texttt{Many} times
to avoid dealing with the complexity of call-by-need semantics, so this program
would not type-check, because $x$ is being consumed \texttt{Many} times instead
of \texttt{1}.
%
\begin{figure}[h]
  \begin{minipage}[l]{0.49\textwidth}
    \begin{code}
    f :: a %1 -> a
    f x = let y = x+2 in y
    \end{code}
  \end{minipage}
  \begin{minipage}[r]{0.49\textwidth}
    \caption{Example Let}
  \end{minipage}
\label{fig:second-motivation}
\end{figure}
%
Despite not being accepted by the surface-level language, linear programs using
lets occur naturally in Core due to optimising transformations that create let
bindings, such as $\beta$-reduction. In a similar fashion, programs which
violate syntactic linearity for other reasons other than let bindings are
produced by Core transformations.

% Therefore, the Core linear type-checker rejects various valid programs after
% desugaring and optimizing transformations, because linearity is seemingly
% violated.
%
The current solution to valid programs being rejected by Core's linear
type-checker is to effectively disable the linear type-checker since,
alternatively, disabling optimizing transformations which violate linearity
incurs significant performance costs.
%
However, we believe that GHC's transformations are correct, and it is the
linear type-checker and its underlying type system that cannot sufficiently
accommodate the resulting programs.

Additionally, some Core-to-Core transformations such as let-floating and
inlining already depend on custom linear type systems to produce more
performant programs. Valid linearity annotations in Core could potentially
inform and define more optimizations.

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

\section{Linearity, Semantically}

\colorbox{working}{A linear type system} statically guarantees that linear resources are
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
Expanding on this, consider above the example program under distinct
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
semantically and syntactically consuming a resource only arises under non-strict semantics.
%
Indeed, under \emph{call-by-value}, syntactic occurrences of a linear resource
directly correspond to semantically using that resource\todo{with the exception
of trivial aliases, maybe not worth mentioning} because \emph{all}
expressions are eagerly evaluated -- if all computations are eagerly run, all
linear resources required by computations are \emph{eagerly consumed}.

\todo[inline]{Não adoro esta secção, parece desconexa, apesar de ser um ponto
fundamental. Acho que tudo à volta precisa de ajudar a empurrar isto.}

\todo[inline]{Re-read little section about linearity and strictness in Linear Haskell}

\todo[inline]{give some call-by-value examples and say how it is probably exactly syntactic linearity}

\todo[inline]{I dislike the current connection between this end and the beginning of the next subsection.}

\subsection{Semantic Linearity by Example\label{sec:semantic-linearity-examples}}

Aligned with our original motivation of typechecking linearity in GHC Core such
that optimising transformations preserve linearity, and with the secondary goal
of understanding linearity in a non-strict context, this section helps the
reader build an intuition for semantic linearity through examples of Core
programs that are semantically linear but rejected by Core's linear type
system.\todo{and possibly by examples of transformations}
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

We start our discussion with non-strict let bindings, i.e. let bindings whose
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
the let body. In the following example, we assign a computation that the resource |x| to a binder which is then returned:
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
According to Linear Haskell's core calculus ~$\lambda_{\to}^{Q}$~\cite{cite:linear-haskell}, let
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
body, however, the resource is still used linearly (semantically) because |y| isn't used at all.
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
optimising compiler will produce intermediate\footnote{Unused bindings are then
also dropped by the optimising compiler} programs with unused bindings
due to transformations such as inlining, which can substitute out occurrences
of the binder (e.g. |y| is inlined in the let body).

Let bindings can also go unused if they are defined before branching on case
alternatives. At runtime, depending on the branch taken, the let binding will
be evaluated only if it occurs in that branch.
Both optimising transformations (float-out), and programmers, can produce
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
once, and re-used subsequently. Despite linear resources in the binder body
just being used to compute a result once, we can only consume the result of the
computation once; perhaps surprisingly, as the perception so far is ``resources
are consumed during computation'', and multiple uses of the same let binder
share the result that was computed only once. In short, the following program
must \emph{not} typecheck:
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
Intuitively, the result of the computation must still be used exactly once,
despite only being effectively computed once, because the result may still
contain (parts of) the linear resource. The trivial example is |f4| applied to
|id| -- the result of computing |id x| is |x|, and |x| must definitely not be
shared! Indeed, if the result of the computation involving the linear resource
was, e.g., an unrestricted integer, then sharing the result would not involve consuming the
resource more than once.\todo{this kind of hints that maybe somehow in the alternative scrutinizing a "trivial" atom we could make the let binding unrestricted after we were sure it was evaluated once, but that isn't easy without erasing too many things before, we kind of tried this once}
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
once. Therefore, let binders depending on linear resources must be used at most
once (are \emph{affine} in the let body).
%
Moreover, if the let binding ($y$) isn't used in the let body, then the
resources it depends on ($\ov{x}$) must be used instead -- the binding $y$ is
mutually exclusive with the resources $\ov{x}$ (for the resources to be used
linearly, either the binder occurs exactly once $y$, or the resources $\ov{x}$
do). We'll later see how we can encode this principle of mutual exclusivity
between let bindings and their dependencies using so called \emph{usage
environments}, in Section~\ref{sec:usage-environments}.

\begin{code}
f :: A -o B -o C
f x y = case (x,y) of z { (a,b) -> ... }
\end{code}

\begin{code}
f :: A -o B -o C
f x y = case something x y of z { (a,b) -> ... }
\end{code}

\begin{code}
f :: A -o B -o C
f x y = case let w = something x y in () of z { () -> ... }
\end{code}

\begin{code}
f :: A -o B -o C
f x y = case () of z { () -> z <> z }
\end{code}

Bad! |x| has already been fully evaluated to K.
\begin{code}
f x = case expensive x of z { K -> x }
\end{code}

This would be fine, but we're not able to see this
\begin{code}
f x = case x of z { K -> x }
\end{code}

We used to call NOT IN WHNF "negative" hah
\begin{code}
-- This is NOT OK since (g x y) is negative (eliminates g)
f x y = case g x y of z
          K1 a b -> (x,y)
          K2 w   -> (x,y)
\end{code}

Getting harder ...

This is not semantically linear!
\begin{code}
f w = case w of z
        (a,b) ->
          case z of z'
            (c,d) ->
               (a,c)
\end{code}

But this is!
\begin{code}
f w = case w of z
        (a,b) ->
          case z of z'
            (c,d) ->
               (a,d)
\end{code}

Bad bad bad! |x| and |y| have been "almost" consumed
\begin{code}
f x y = let w = use x y
         in case h x y of
              K a b ->
                return w
\end{code}

We say "almost", because they still need to be "fully consumed" by means of the pattern variables or case binder.
i.e. this is not linear:
\begin{code}
f x y = let w = use x y
         in case h x y of
              K a b -> ()
\end{code}

the harder ones regarding reverse binder swap. these give some intuition, but this is an unsound optimisation it seems

\begin{code}
f y = let x = use y
       in case x of z { K a b -> expensive x; K2 w -> w }
\end{code}

\begin{code}
f y = let x = use y
      let t = expensive x
       in case x of z { K a b -> t; K2 w -> w }
\end{code}

\begin{code}
f x = case x of z { K a b -> expensive x; K2 w -> w }


f y = let x = use y
       in case x of z { K a b -> expensive x; K2 w -> w }


f y = let x = use y
      let t = expensive x
       in case x of z { K a b -> t; K2 w -> w }
\end{code}

\subsection{Call-by-need lets and cases}

\todo[inline]{Não sei se falo nesta secção apenas de avaliação Call by need ou
se falo já de Core constructs e da forma como eles são avaliados. Se falo de
WHNF e NF e HNF? já, ou mais tarde $\dots$}

\todo[inline]{Introduce Haskell Core, talk about when things are consumed?}

\subsection{Generalizing}

We propose a generalization of the definition of consuming a resource in terms of evaluation:

Definition X.Y: A linear resource is consumed when it is either fully evaluated
(NF) to a value, or when it is returned s.t. an application of that function
being fully evaluated would fully evaluate the resource to a value. Or something like that.

Note how this generalizes Linear Haskell's definition of consuming a resource: $\dots$

(We note the rare exception of pure aliasing in call-by-value languages not captured by this def.)

\todo[inline]{We could almost say that eventually everything all linear
resources must be evaluated to NF to be consumed, or returned by a function
s.t. a continuation of that function has to evaluate the result to NF., or something.}

\todo[inline]{Discuss definition of consuming resources of linear haskell}
\todo[inline]{Discuss our own generalized (call-by-value, call-by-name, etc)
definition of consuming resources by evaluation. Something like, if an
expression is fully evaluated, all linear resources that expression depends on
to compute a result are consumed, or something...}
  
\subsection{Leftover}

\todo[inline]{unrestricted call-by-name with resources can duplicate the resources, as if it were unsound?}

\todo[inline]{Quanto é que eu devia falar de call-by-need labmda calculus sem
cases? não é mt interessante, pq as exps avaliadas sao sempre avaliadas pra
funcções (e arg) -> (e' arg), e por isso os recursos são todos completamente
consumidos. A questão de WHNF e assim só aparece mais à frente; mas se calhar serve de começo?}

\subsection{Linearity and strictness}

maybe. see also section of the same name in Linear Haskell

\section{Typechecking Linearity in Core}

\todo[inline]{We kind of ignore the multiplicity semiring. We should discuss
how we don't do ring operations ... but that's kind of wrong.}

In this section, we develop a linear calculus titled \emph{Linear Core} that 
combines the linearity-in-the-arrow and multiplicity polymorphism introduced by
Linear Haskell~\cite{linearhaskell} with all the key features from GHC's Core
language, except for type equality coercions\footnote{We explain a main avenue of
future work, multiplicity coercions, in Section~\ref{sec:future-work}}.
%
Specifically, our core calculus is a linear lambda calculus with
algebraic datatypes, case expressions, recursive let bindings, and multiplicity
polymorphism.

Linear Core makes precise the various insights discussed in the previous
section by putting them together in a linear type system for which we prove
soundness via the common preservation and progress theorems. Crucially, the
Linear Core type system accepts all the \emph{semantically linear} example
programs from Section~\ref{sec:semantic-linearity-examples} that Core currently
rejects.
 
% We start by introducing the Core-like language, $\dots$ usage environments as a
% way to encode choice between the way a resource is used $\dots$\todo{$\dots$}

We also note that despite the focus on GHC Core, the fundamental ideas for
understanding linearity in a call-by-need calculus can be readily applied to
other call-by-need languages.\todo{make better sentence?}

\todo[inline]{Explicar algumas das ideias fundamentais, e apresentar as regras
iterativamente. Podemos começar com as triviais e avançar para os dois pontos
mais difíceis : Lets e Cases}

\subsection{Linear Core Overview}

\emph{Linear Core} is a 

\todo[inline]{Syntax, examples}

\todo[inline]{Remember to mention we assume all patterns are exhaustive}

\subsection{Usage environments\label{sec:usage-environments}}

\todo[inline]{Usage environments as a way to encode mutual exclusivity between
using a variable and the resources it is comprised of. Explain definition, it
is literally the variables used to type the binder in the case of the let. A
bit more complicated for cases i.e. "which resources are we using when using
the case-binder? effectively, the scrutinee. what about case pat vars?..." and
so on}

\subsection{Lazy let bindings}

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

\subsection{Case expressions evaluate to WHNF}

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

\section{Metatheory}

\todo[inline]{Consider making type safety and optimizations a section of their
own, so we can have a reverse-binder-swap subsection}

\subsection{Type safety}

\todo[inline]{We proved soundness of our system...}
\todo[inline]{The harder cases are for the interesting ones - lets, cases, and case alternatives}

\subsection{Optimisations preserve linearity}

\subsubsection{Inlining}

To the best of our knowledge, there is no linear type system for which inlining
preserves linearity\footnote{https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0111-linear-types.rst\#id90}

\todo[inline]{We proved multiple optimizing transformations preserve linearity}

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

\section{Syntax Directed System}

\todo[inline]{In the other system we assume that the recursive lets are strongly connected, i.e. the expressions always}

\input{language-v4/SyntaxDirectedSystem}

\subsection{Inferring usage environments}

\todo[inline]{The difference between this and the previous section is a bit blurry}

\todo[inline]{There's one more concern: usage environments aren't readily
available, especially in recursive lets. We must perform inference of usage
environments before we can typecheck using them. This is how:}

\todo[inline]{Rather, we define a syntax directed type system that infers usage environments while checking...}

\section{Implementation}


