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

\section{Consuming resources under call-by-need}

A linear type system statically guarantees that linear resources are
\emph{consumed} exactly once. Consequently, whether a program is well-typed
under a linear type system intrisically depends on the precise definition of
\emph{consuming} a resource. Even though \emph{consuming} a resource is commonly regarded
as synonymous with \emph{using} a resource, i.e. with the syntatic occurrence
of the resource in the program, that is not always the case.
%
In fact, this section highlights the distinction between using resources
syntatically and semantically as a principal limitation of linear type
systems for (especially) non-strict languages.

% and we show how a linear type system found on
% \emph{consuming resources semantically} rather than \emph{using resources
% syntatically} can accept

Consider, for example, the following program in a functional pseudo-language,
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
computation is run (i.e. evaluated).
%
The example illustrates how \emph{consuming} a resource is not necessarily
synonymous with using it syntatically, as depending on the evaluation strategy
of the pseudo-language, the computation that closes the handle might or not be
evaluated, and if it isn't, the |handle| in that unused computation
is not consumed.
%
Expanding on the same example program, consider it under distinct evaluation strategies:
%
\begin{description}

\item[Call-by-value] With \emph{eager} evaluation, the let bound expression |close
handle| is eagerly evaluated, and the |handle| will be closed before being
returned. It is clear that a linear type system should not accept such a
program since the linear resource |handle| is duplicated -- it is used a
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
%Rather, \emph{consuming} a resource is intrisically defined by the evaluation model of the language.
%
% Under distinct evaluation strategies, the above example (and programs in general) have different semantics:
%
%
Intuitively, a computation that depends on a linear resource to produce a
result consumes that resource iff the result is effectively computed; in
contrast, a computation that depends on a linear resource but is never run,
will not consume that resource.

From this observation, and exploring the connection between computation and evaluation,\todo{Alguma dificuldade em dizer exatamente como é que evaluation drives/is computation}
it becomes clear that \emph{linearity} and \emph{consuming resources}, in the
above example and programs in general, should be defined in function of the
language's evaluation strategy.

\todo[inline]{Re-read little section about linearity and strictness in Linear Haskell}

\todo[inline]{We could almost say that eventually everything all linear
resources must be evaluated to NF to be consumed, or returned by a function
s.t. a continuation of that function has to evaluate the result to NF., or something.}

\todo[inline]{give some call-by-value examples and say how it is probably exactly syntatic linearity}

\subsection{Call-by-need with case expressions?}
\todo[inline]{Introduce Haskell Core, talk about when things are consumed}

\subsection{Generalizing}

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

\section{Typechecking Linearity in Core}

In this section, we develop a linear calculus titled \emph{Linear Core} that 
combines the linearity-in-the-arrow and multiplicity polymorphism introduced by
Linear Haskell~\cite{linearhaskell} with all the key features from GHC's Core
language, except for type equality coercions\footnote{We explain a main avenue of
future work, multiplicity coercions, in Section~\ref{sec:future-work}}.
%
Specifically, our core calculus system is a linear lambda calculus with
algebraic datatypes, case expressions, recursive let bindings, and multiplicity
polymorphism.
 
We start by introducing the Core-like language, $\dots$ usage environments as a
way to encode choice between the way a resource is used $\dots$
%
We also note that, despite the focus on GHC Core's linearity, the fundamental
ideas for understanding linearity in a call-by-need calculus can be readily
applied to other call-by-need languages.\todo{make better sentence}

\todo[inline]{Explicar algumas das ideias fundamentais, e apresentar as regras
iterativamente. Podemos começar com as triviais e avançar para os dois pontos
mais difíceis : Lets e Cases}

\subsection{Linear Core}

\todo[inline]{Syntax, examples}

\todo[inline]{Remember to mention we assume all patterns are exhaustive}

\subsection{Usage environments}

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

\subsection{Optimizations}

\todo[inline]{We proved multiple optimizing transformations preserve linearity}

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


