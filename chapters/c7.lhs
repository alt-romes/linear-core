%include polycode.fmt

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

\section{Lazy Linearity}

\todo[inline]{A section in main chapter could be named how linearity interacts with lazy/Haskell's/call-by-need evaluation}

\section{Typechecking Linearity in Core}

\todo[inline]{Explicar algumas das ideias fundamentais, e apresentar as regras
iterativamente. Podemos começar com as triviais e avançar para os dois pontos
mais difíceis : Lets e Cases}

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


