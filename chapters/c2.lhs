%include polycode.fmt

\chapter{Background\label{sec:background}}

In this section we review the concepts required to understand our work. In
short, we discuss linear types, the Haskell programming language, linear types
as they exist in Haskell (dubbed Linear Haskell), evaluation strategies,
Haskell's main intermediate language (Core) and its formal foundation (System
$F_C$) and, finally, an overview of GHC's pipeline with explanations of
multiple Core-to-Core optimising transformations that we prove type-preserving
in our type system.

\section{Linear Types\label{sec:linear-types}}

Much the same way type systems can statically eliminate various kinds of
programs that would fail at runtime, such as a program that dereferences an
integer value rather than a pointer, linear type systems can guarantee that
certain errors (regarding resource usage) are forbidden.

In linear type systems~\cite{cite:linear-logic,cite:barberdill}, so called
linear resources must be used \emph{exactly once}. Not using a linear resource
at all or using said resource multiple times will result in a type error. We can
model many real-world resources such as file handles, socket descriptors, and
allocated memory, as linear resources. This way, because a file handle must be
used exactly once, forgetting to close the file handle is a type error, and
closing the handle twice is also a type error.  With linear types, avoiding
leaks and double frees is no longer a programmer's worry because the compiler
can guarantee the resource is used exactly once, or \emph{linearly}.

To understand how linear types are defined and used in practice, we present two
examples of anonymous functions that receive a handle to work with (that must be
closed before returning), we explore how the examples could be disregarded as
incorrect, and work our way up to linear types from them. The first function
ignores the received file handle and returns $\star$ (read unit), which is
equivalent to C's \texttt{void}.
%
\begin{mathpar}
    \lambda h.~\mathsf{return}~\star;
    \and
    \lambda h.~\mathsf{close}~h;~\mathsf{close}~h;
\end{mathpar}

Ignoring the file handle which should have been closed by the function makes the
first function incorrect. Similarly, the second function receives the file
handle and closes it twice, which is incorrect not because it falls short of the
specification, but rather because the program will crash while executing it.
%
Additionally, both functions share the same type, $\texttt{Handle} \to \star$,
i.e.  a function that takes a \texttt{Handle} and returns $\star$. The second
function also shares this type because \texttt{close} has type $\texttt{Handle}
\to \star$.
%
Under a simple type system such as C's, both functions are type correct (the
compiler will happily succeed), but both have erroneous behaviours. The first
forgets to close the handle and the second closes it twice. Our goal is to reach
a type system that rejects these two programs.

The key observation to invalidating these programs is to focus on the function
type going between \texttt{Handle} and $\star$ and augment it to indicate that
\emph{the argument must be used exactly once}, or, in other words, that the
argument of the function must be linear. We take the function type $A \to B$
and replace the function arrow ($\to$) with the linear function arrow ($\lolli$)\footnote{Since linear types are born from a correspondence with linear
logic~\cite{cite:linear-logic} (the Curry-Howard isomorphism~\cite{curry:34,howard:80}), we
borrow the $\lolli$ symbol and other linear logic connectives to describe linear
types.}
%
operator to denote a function that uses its argument exactly once: $A \lolli B$.
%
Providing the more restrictive linear function signature $\texttt{Handle} \lolli
\star$ to the example programs would make both of them fail to typecheck because
they do not satisfy the linearity specification that the function argument
should only be used exactly once.

% Linear types are a powerful idea because they allow us to statically reason
% about resources in our program. A so called linear resource ?

In order to further give well defined semantics to a linear type system, we
present a linearly typed lambda
calculus~\cite{cite:linear-logic,cite:barberdill}, a very simple language with
linear types, by defining what are syntactically valid programs through the
grammar in Fig.~\ref{fig:llcgrammar} and what programs are well typed through
the typing rules in Fig.~\ref{fig:llcrules}. The language features functions
and function application ($\lolli$), two flavours of pairs, additive ($\with$)
and multiplicative ($\tensor$), a disjunction operator ($\oplus$) to construct
sum types, and the $\bang$ modality operator which constructs an unrestricted
type from a linear one, allowing values inhabiting $\bang A$ to be consumed
unrestrictedly. A typing judgement for the linearly typed lambda calculus has
the form
%
\[ \Gamma; \Delta \vdash M : A \]
%
where $\Gamma$ is the context of resources that may be used unrestrictedly,
that is, any number of times, $\Delta$ is the context of resources that must be
used linearly (\emph{exactly once}), $M$ is the program to type and $A$ is its
type.  When resources from the linear context are used, they are removed from
the context and no longer available, and all resources in the linear context
must be used exactly once.

\begin{figure}[h]
\[
\begin{array}{c}
  \begin{array}{lcl}
    A,B & ::= & \star\\
        & \mid & A \lolli B\\
        & \mid & A \oplus B\\
        & \mid & A \tensor B\\
        & \mid & A \with B\\
        & \mid & \bang A\\
   \end{array}
\qquad
  \begin{array}{lcl}
      M,N & ::= & \star \mid \llet{\star = M}{N} \\
        & \mid & u \\
        & \mid & \lambda u. M \mid M~N\\
        & \mid & \textrm{inl}~M \mid \textrm{inr}~M\\
        & \mid & \ccase{M}{\textrm{inl}~u_1 \to N_1;\textrm{inr}~u_2 \to N_2}\\
        & \mid & M \tensor N \mid \llet{u_1 \tensor u_2 = M}{N}\\
        & \mid & M \with N \mid \textrm{fst}~M \mid \textrm{snd}~M \\
        & \mid & \bang M \mid \llet{!u = M}{N} \\
   \end{array}
\end{array}
\]
\caption{Grammar for a linearly-typed lambda calculus}
\label{fig:llcgrammar}
\end{figure}

The function abstraction is typed according to the linear function introduction
rule ($\lolli I$). The rule states that a function abstraction, written
$\lambda u. M$, is a linear function (i.e. has type $A \lolli B$) given the
unrestricted context $\Gamma$ and the linear context $\Delta$, if the program $M$
has type $B$ given the same unrestricted context $\Gamma$ and the linear context
$\Delta,u{:}A$. That is, if $M$ has type $B$ using $u$ of type $A$ exactly once
besides the other resources in $\Delta$, then the lambda abstraction has the
linear function type.
%
\[
    \infer*[right=($\lolli I$)]
    {\Gamma ; \Delta , u{:}A \vdash M : B}
    {\Gamma ; \Delta \vdash \lambda u. M : A \lolli B}
\qquad
    \infer*[right=($\lolli E$)]
    {\Gamma ; \Delta \vdash M : A \lolli B \and \Gamma ; \Delta' \vdash N : A}
    {\Gamma ; \Delta, \Delta' \vdash M~N : B}
\]
%
Function application is typed according to the elimination
rule for the same type ($\lolli E$). To type an application $M~N$ as $B$, $M$
must have type $A \lolli B$ and $N$ must have type $A$. To account for the
linear resources that might be used while proving both that $M{:}A \lolli B$ and
$N{:}A$, the linear context must be split in two such that both typing judgments
succeed using exactly once every resource in their linear context (while the
resources in $\Gamma$ might be used unrestrictedly), hence the separation of the
linear context in $\Delta$ and $\Delta'$.

The multiplicative pair ($M \tensor N$) is constructed from two linearly typed expressions that
can each be typed with a division of the given linear context, as we see in its
introduction rule ($\tensor I$). Upon deconstruction, the multiplicative pair
elimination rule ($\tensor E$) requires that both of the pair constituents be
consumed exactly once.
%
\[
    \infer[($\tensor I$)]
    {\Gamma ; \Delta \vdash M : A \and \Gamma ; \Delta' \vdash N : B}
    {\Gamma ; \Delta , \Delta' \vdash (M \tensor N) : A \tensor B}
\qquad
    \infer[($\tensor E$)]
    {\Gamma ; \Delta \vdash M : A \tensor B \and \Gamma ; \Delta', u{:}A, v{:}B \vdash N : C}
    {\Gamma ; \Delta , \Delta' \vdash \llet{u \tensor v}{N} : C}
\]
%
On the other hand, the additive pair requires that both elements of the pair can
be proved with the same linear context, and upon deconstruction only one of the
pair elements might be used, rather than both simultaneously.

Finally, the "of-course" operator ($\bang$) can be used to construct a resource that can be
used unrestrictedly ($\bang M$). Its introduction rule ($\bang I$) states that
to construct this resource means to add a resource to the unrestricted context,
which can then be used freely. To construct an unrestricted value, however, the
linear context \emph{must be empty} -- an unrestricted value can only be constructed if
it does not depend on any linear resource.
%
\[
    \infer*[right=($\bang I$)]
    {\Gamma ; \cdot \vdash M : A}
    {\Gamma ; \cdot \vdash !M : !A}
\qquad    \infer*[right=($\bang E$)]
    {\Gamma ; \Delta \vdash M : \bang A \and \Gamma, u{:}A ; \Delta' \vdash N : C}
    {\Gamma ; \Delta, \Delta' \vdash \llet{!u = M}{N} : C}
\]
%
To utilize an unrestricted value $M$, we must bind it to $u$ with $\llet{\bang u
= M}{N}$ which can then be used in $N$ unrestrictedly, because $u$ extends the
unrestricted context rather than the linear context as we have seen thus far.

In Section~\ref{sec:linear-haskell}, we describe how linear types are defined in
Haskell, a programming language more \emph{featureful} than the linearly typed lambda
calculus. We will see that the theoretical principles underlying the linear
lambda calculus and linear Haskell are the same, and by studying them in this
minimal setting we can understand them at large.

\begin{figure}[h]
{\small
  \[
  \begin{array}{c}
    \infer*[right=($u$)]
    { }
    {\Gamma ; u{:}A \vdash u : A}
\qquad
    \infer*[right=($u$)]
    { }
    {\Gamma , u{:}A ; \cdot \vdash u : A}
\\[1em]
    \infer*[right=($\tensor I$)]
    {\Gamma ; \Delta \vdash M : A \and \Gamma ; \Delta' \vdash N : B}
    {\Gamma ; \Delta , \Delta' \vdash (M \tensor N) : A \tensor B}
\quad
    \infer*[right=($\tensor E$)]
    {\Gamma ; \Delta \vdash M : A \tensor B \and \Gamma ; \Delta', u{:}A, v{:}B \vdash N : C}
    {\Gamma ; \Delta , \Delta' \vdash \llet{u \tensor v}{N} : C}
\\[1em]
    \infer*[right=($\lolli I$)]
    {\Gamma ; \Delta , u{:}A \vdash M : B}
    {\Gamma ; \Delta \vdash \lambda u. M : A \lolli B}
\qquad
    \infer*[right=($\lolli E$)]
    {\Gamma ; \Delta \vdash M : A \lolli B \and \Gamma ; \Delta' \vdash N : A}
    {\Gamma ; \Delta, \Delta' \vdash M~N : B}
\\[1em]
    \infer*[right=($\with I$)]
    {\Gamma ; \Delta \vdash M : A \and \Gamma ; \Delta \vdash N : B}
    {\Gamma ; \Delta \vdash M \with N : A \with B}
\quad
    \infer*[right=($\with E_L$)]
    {\Gamma ; \Delta \vdash M : A \with B}
    {\Gamma ; \Delta \vdash \textrm{fst}~M : A}
\quad
    \infer*[right=($\with E_R$)]
    {\Gamma ; \Delta \vdash M : A \with B}
    {\Gamma ; \Delta \vdash \textrm{snd}~M : B}
\\[1em]
    \infer*[right=($\oplus I_L$)]
    {\Gamma ; \Delta \vdash M : A}
    {\Gamma ; \Delta \vdash \textrm{inl}~M : A \oplus B}
\qquad
    \infer*[right=($\oplus I_R$)]
    {\Gamma ; \Delta \vdash M : B}
    {\Gamma ; \Delta \vdash \textrm{inr}~M : A \oplus B}
\\[1em]
    \infer*[right=($\oplus E$)]
    {\Gamma ; \Delta \vdash M : A \oplus B \and \Gamma ; \Delta', w_1{:}A \vdash N_1 : C \and
    \Gamma ; \Delta', w_2{:}B \vdash N_2 : C}
    {\Gamma ; \Delta, \Delta' \vdash \ccase{M}{\textrm{inl}~w_1 \to N_1 \mid \textrm{inr}~w_2 \to N_2} : C}
\\[1em]
    \infer*[right=($\star I$)]
    { }
    {\Gamma ; \cdot \vdash \star : \star}
\quad    \infer*[right=($\star E$)]
    {\Gamma ; \Delta \vdash M : \star \and \Gamma ; \Delta' \vdash N : B}
    {\Gamma ; \Delta, \Delta' \vdash \llet{\star = M}{N} : B}
\\[1em]
    \infer*[right=($\bang I$)]
    {\Gamma ; \cdot \vdash M : A}
    {\Gamma ; \cdot \vdash !M : !A}
\qquad    \infer*[right=($\bang E$)]
    {\Gamma ; \Delta \vdash M : \bang A \and \Gamma, u{:}A ; \Delta' \vdash N : C}
    {\Gamma ; \Delta, \Delta' \vdash \llet{!u = M}{N} : C}
  \end{array}
\]}
\caption{Typing rules for a linearly-typed lambda calculus}
\label{fig:llcrules}
\end{figure}

% % \begin{code}
% % let p = malloc(5)
% %     p' = store(p, "x")
% %     (p'', v) = load(p)
% %     free p''
% % \end{code}

% % We'd like to hide the boilerplate involved \cite{Linear constraints}

\section{Haskell}

Haskell is a functional programming language defined by the Haskell
Report~\cite{jones1999haskell,marlow2010haskell} and whose \emph{de-facto}
implementation is GHC, the Glasgow Haskell Compiler~\cite{marlow2012the}. Haskell is a
\emph{lazy}, \emph{purely functional} language, i.e., functions cannot
have side effects or mutate data, and, contrary to many programming languages,
arguments are \emph{not} evaluated when passed to functions, but rather are only
evaluated when its value is needed. The combination of purity and laziness is
unique to Haskell among mainstream programming languages.

Haskell is a large feature-rich language but its relatively small core is based
on a typed lambda calculus. As such, there exist no statements and computation
is done simply through the evaluation of functions. Besides functions, one can
define types and their constructors and pattern match on said constructors.
Function application is denoted by the juxtaposition of the function expression
and its arguments, which often means empty space between terms (\texttt{f~a}
means \texttt{f} applied to \texttt{a}). Pattern matching is done with the
\texttt{case} keyword followed by the enumerated alternatives. All variable
names start with lower case and types start with upper case (excluding type
variables). To make explicit the type of an expression, the \texttt{::} operator
is used (e.g.  $\texttt{f~::~Int}\to \texttt{Bool}$ is read \texttt{f} \emph{has
type} function from \texttt{Int} to \texttt{Bool}).

Because Haskell is a pure programming language, input/output side-effects are
modelled at the type-level through the non-nullary\footnote{\texttt{IO} has kind $\texttt{Type}\to\texttt{Type}$, that is, it is
only a type after another type is passed as a parameter (e.g.  \texttt{IO~Int},
\texttt{IO~Bool}); \texttt{IO} by itself is a \emph{type constructor}}
%
type constructor \texttt{IO}. A value of type \texttt{IO~a} represents a
\emph{computation} that when executed will perform side-effects and produce a
value of type \texttt{a}. Computations that do I/O can be composed into larger
computations using so-called monadic operators, which are like any other
operators but grouped under the same abstraction.
%
Some of the example programs will look though as if they had statements, but,
in reality, the sequential appearance is just syntactic sugar to an expression
using monadic operators. The main take away is that computations that do I/O
may be sequenced together with other operations that do I/O while retaining the
lack of statements and the language purity guarantees.

% TODO: Perhaps elaborate a bit more on the constructors and pattern matching?

As an example, consider these functions that do I/O and their types. The first
opens a file by path and returns its handle, the second gets the size of a file
from its handle, and the third closes the handle. It is important that the
handle be closed exactly once, but currently nothing in the type system
enforces that usage policy.

\begin{code}
openFile :: FilePath -> IOMode -> IO Handle
hFileSize :: Handle -> IO Integer
hClose   :: Handle -> IO ()
\end{code}

The following function makes use of the above definitions to return the size of
a file given its path. Note that the function silently leaks the handle to the
file, despite compiling successfully. In this example Haskell program, the use
of linear types could eventually prevent the handle from being leaked by
requiring it to be used exactly once.

\begin{code}
countWords :: FilePath -> IO Integer
countWords path = do
    handle <- openFile path ReadMode
    size   <- hFileSize handle
    return size
\end{code}
% hClose handle

Another defining feature of Haskell is its powerful type system. In contrast to
most mainstream programming languages, such as OCaml and Java, Haskell supports a myriad of
advanced type level features, such as:
\begin{itemize}

    \item Multiple forms of advanced polymorphism: where languages with whole
        program type inference usually stick to Damas–Hindley–Milner type
        inference~\cite{DBLP:conf/popl/DamasM82}, Haskell goes much further with, e.g.,
        arbitrary-rank types~\cite{10.1017/S0956796806006034}, type-class
        polymorphism~\cite{10.1145/227699.227700}, levity polymorphism~\cite{10.1145/3062341.3062357},
        multiplicity polymorphism~\cite{cite:linearhaskell}, and, more recently, impredicative
        polymorphism~\cite{10.1145/3408971}.

    \item Type level computation by means of type
        classes~\cite{10.1007/3-540-57880-3_16} and Haskell's type
        families~\cite{10.1145/1090189.1086397,10.1145/1040305.1040306,10.1145/2633357.2633361},
        which permit a direct encoding of type-level functions resembling rewrite
        rules.

    \item Local equality constraints and existential types by using GADTs, which
        we explain ahead in more detail. A design for first class existential
        types with bi-directional type inference in Haskell has been published
        in~\cite{10.1145/3473569}, despite not being yet implemented in GHC.

\end{itemize}
% Haskell's type families, supports abstraction through type classes, and GADTs
% which we explain in more detail ahead.  as type classes, arbitrary-rank types,
% functional dependencies, GADTs, type families and (more recently) even
% impredicative polymorphism\cite{}
These advanced features have become commonplace in Haskell code, enforcing
application level invariants and program correctness through the types. As an
example to work through this section while we introduce compile-time invariants
with GADTs, consider the definition of \texttt{head} in the standard library, a
function which takes the first element of a list by pattern matching on the list
constructors.

\begin{code}
    head :: [a] -> a
    head [] = error "List is empty!"
    head (x:xs) = x
\end{code}

When applied to the empty list, \texttt{head} terminates the program with an
error. This function is unsafe -- our program might crash if we use it on an
invalid input.
%
Leveraging Haskell's more advanced features, we can use more expressive types to
assert properties about the values and get rid of the invalid cases (e.g. we
could define a \texttt{NonEmpty} type to model a list that can not be empty).
%
A well liked motto is "make invalid states unrepresentable". In this light, we
introduce Generalized Algebraic Data Types (GADTs) and create a list type
indexed by size for which we can write a completely safe \texttt{head} function
by expressing that the size of the list must be at least one, at the type level.

% Unfortunate we have to comment this! We lose a reference to Ghengin :)
%%% \subsection{Generalized Algebraic Data Types\label{sec:background-gadts}}
%%% 
%%% \textbf{GADTs}~\cite{Cheney2003FirstClassPT,10.1145/1159803.1159811,cite:outsideinx} are an advanced Haskell feature
%%% that allows users to define data types as they would common algebraic data
%%% types, with the added abilitiy to give explicit type signatures for the data
%%% constructors where the result type may differ in the type parameters (e.g., we
%%% might have two constructors of the same data type \texttt{T~a} return values of
%%% type \texttt{T~Bool} and \texttt{T~Int}).
%%% %
%%% This allows for additional type invariants to be represented with GADTs through
%%% their type parameters, which restricts the use of specific constructors and
%%% their subsequent deconstruction through pattern matching.
%%% %
%%% % TODO: Rewrite this bit below
%%% Pattern matching against GADTs can introduce local type refinements, i.e.
%%% refine the type information used for typechecking individual case alternatives.
%%% We develop the length-indexed lists example without discussing the type system
%%% and type inference details of GADTs as desribed in~\cite{cite:outsideinx}.
%%% % which we later explore in~\ref{related-work-gadts}.
%%% 
%%% % First, we define the natural numbers inductively: a natural number is either
%%% % zero (\texttt{Z}) or a successor (\texttt{S}) of another natural number (e.g.
%%% % the successor of the successor of zero is a natural number). The following
%%% % definition creates the \texttt{Nat} type, the \texttt{Z} and \texttt{S} data
%%% % constructors which construct values, \emph{and} the \texttt{Z} and \texttt{S}
%%% % \emph{type} constructors which construct types.
%%% % %
%%% % % The latter two exist because of the \emph{DataKinds} language feature which
%%% % % promotes term-level constructors to type-level constructors.
%%% % 
%%% % \begin{code}
%%% %     data Nat = Z | S Nat
%%% %   \end{code}
%%% 
%%% We define the data type in GADT syntax for length-index lists which
%%% takes two type parameters. The first type parameter is the length of the list
%%% and the type of the type parameter (i.e. the kind of the first type parameter)
%%% is \texttt{Nat}. To construct a type of kind \texttt{Nat} we can only use the
%%% type constructors \texttt{Z} and \texttt{S}. The second type parameter is the
%%% type of the values contained in the list, and any type is valid, hence the
%%% \texttt{Type} kind.
%%% 
%%% \begin{code}
%%%     data Vec (n :: Nat) (a :: Type) where
%%%         Nil :: Vec Z a
%%%         Cons :: a -> Vec m a -> Vec (S m) a
%%% \end{code}
%%% 
%%% The length-indexed list is defined inductively as either an empty list \emph{of
%%% size zero}, or the construction of a list by appending a new element to an
%%% existing list \emph{of size $m$} whose final size is $m+1$ (\texttt{S m}). The
%%% list \texttt{Cons~'a'~(Cons~'b'~Nil)} has type \texttt{Vec~(S~(S~Z))~Char}
%%% because \texttt{Nil} has type \texttt{Vec~Z~Char} and \texttt{Cons~'a'~Nil} has
%%% type \texttt{Vec~(S~Z)~Char}.
%%% GADTs make possible different data constructors being parametrized over
%%% different type parameters as we do with \texttt{Vec}'s size parameter being
%%% different depending on the constructor that constructs the list.
%%% 
%%% To define the safe \texttt{head} function, we must specify the type of the input
%%% list taking into account that the size must not be zero. To that effect, the
%%% function takes as input a \texttt{Vec (S n) a}, that is, a vector with size
%%% (n+1) for all possible n's. This definition makes a call to \texttt{head} on a list of type
%%% \texttt{Vec Z a} (an empty list) a compile-time type error.
%%% 
%%% \begin{code}
%%%     head :: Vec (S n) a -> a
%%%     head (Cons x xs) = x
%%% \end{code}
%%% 
%%% Pattern matching on the \texttt{Nil} constructor is not needed, despite it
%%% being a constructor of \texttt{Vec}. The argument type doesn't match the type
%%% of the \texttt{Nil} constructor ($\texttt{S~n} \neq \texttt{Z}$), so the
%%% corresponding pattern case alternative is innacessible because the typechecker
%%% does not allow calling \texttt{head} on \texttt{Nil} (once again, its type,
%%% \texttt{Vec~Z~a}, does not match the input type of \texttt{head},
%%% \texttt{Vec~(S~n)~a}).
%%% 
%%% In practice, the idea of using more expressive types to enforce invariants at
%%% compile time, that is illustrated by this simple example, can be taken much
%%% further, e.g., to implement type-safe artificial neural
%%% networks~\cite{cite:practicaldependenttypesinhaskell},
%%% enforce size compatibility in operations between matrices and
%%% vectors~\cite{cite:hmatrix}, to
%%% implement red-black trees guaranteeing its invariants at compile-time, or to
%%% implement a material system in a game engine~\cite{cite:ghengin}.
%%% % TODO: cite: https://blog.jle.im/entry/practical-dependent-types-in-haskell-1.html
%%% % TODO: haskell-servant?
%%% 
%%% Linear types are, similarly, an extension to Haskell's type system that makes it
%%% even more expressive, by providing a finer control over the usage of certain
%%% resources at the type level.
%%% \todo[inline]{As we'll see after introducing linear
%%% haskell and multiplicities, GADTs/local equality evidence and multiplicity
%%% polymorphism interact in a non-trivial manner, and the way }

% TODO:
% Is it outside the scope of this report to discuss the merits and disadvantages
% of laziness and purely functional properties?

% \begin{itemize}
    % \item Features fundamentais
    % \item Exemplos, introduzir syntax
    % \item (Ao contrário de OCaml) tem um sistema de tipos muito sofisticado
    % \item Eventualmente explicação de GADTs? c/ exemplo do Vec
    % \item Uma das features mais avaçadas/experimentais é o Linear Haskell
% \end{itemize}

\section{Linear Haskell\label{sec:linear-haskell}}

% Introduction of linear types to Haskell. How do they work, what's the syntax?
% Multiplicities, examples. Monads, multiplicity polymorphism, multiplicity
% polymoprhism applied to monadic bind to define resource-aware sequencing of
% operations. Linear haskell relates systemFC with the linear lambda calculus?

The introduction of linear types to Haskell's type system is originally
described in Linear Haskell~\cite{cite:linearhaskell}. While in
Section~\ref{sec:related-work-linear-haskell} we discuss the reasoning and
design choices behind retrofitting linear types to Haskell, here we focus on
linear types solely as they exist in the language, and rework the file handle
example seen in the previous section to make sure it doesn't typecheck when the handle is forgotten.

A linear function ($f :: A \lolli B$) guarantees that if ($f~x$) is consumed
exactly once, then the argument $x$ is consumed exactly once. The precise
definition of \emph{consuming a value} depends on the value as follows,
paraphrasing Linear Haskell~\cite{cite:linearhaskell}:

\begin{itemize}
    \item To consume a value of atomic base type (such as~\texttt{Int} or
        \texttt{Ptr}) exactly once, just evaluate~it.
    \item To consume a function value exactly once, apply it to one argument,
        and consume its result exactly once.
    \item To consume a value of an algebraic datatype exactly once,
        pattern-match on it, and consume all its linear components exactly once.
        For example, a linear pair (equivalent to $\tensor$) is consumed exactly
        once if pattern-matched on \emph{and} both the first and second element are
        consumed once.
\end{itemize}

% \todo[pink, inline]{Either hint at a the importance of the definition of
% consuming values and expressions here, or be very clear about it in the Linear
% Core section}

In Haskell, linear types are introduced through \emph{linearity on the function
arrow}.
In practice, this means function types are annotated with a linearity that
defines whether a function argument must be consumed \emph{exactly once} or
whether it can be consumed \emph{unrestrictedly} (many times).
%
As an example, consider the function $f$ below, which doesn't typecheck because
it is a linear function (annotated with \texttt{1}) that consumes its argument
more than once, and the function $g$, which is an unrestricted function
(annotated with \texttt{Many}) that typechecks because its type allows the
argument to be consumed unrestrictedly.

\begin{minipage}{0.47\textwidth}
\begin{code}
    f :: a %1 -> (a, a)
    f x = (x, x)
\end{code}
\end{minipage}
\begin{minipage}{0.47\textwidth}
\begin{code}
    g :: a %Many -> (a, a)
    g x = (x, x)
\end{code}
\end{minipage}

The function annotated with the \emph{multiplicity} annotation of \texttt{1} is
equivalent to the linear function type ($\lolli$) seen in the linear lambda
calculus~(\Cref{sec:linear-types}).
%
Additionally, algebraic data type constructors can specify whether their
arguments are linear or unrestricted, requiring that, when pattern matched on,
linear arguments be consumed once while unrestricted arguments need not be
consumed exactly once.
%Similarly, when constructing such a constructor, using a linear value as a
%linear argument of the constructor consumes it once, while using it as an
%unrestricted argument consumes it unrestrictedly.
%
To encode the multiplicative linear pair ($\tensor$) we must create a pair data
type with two linear components. To consume an algebraic data type is to
consume all its linear components once, so, to consume said pair data type, we
need to consume both its linear components -- successfully encoding the
multiplicative pair elimination rule ($\tensor E$). To construct said pair data
type we must provide two linear elements, each consuming some required
resources to be constructed, thus encoding the multiplicative pair introduction
rule ($\tensor I$). As such, we define \texttt{MultPair} as an algebraic data
type whose constructor uses a linear arrow for each of the
arguments\footnote{By default, constructors defined without GADT syntax have
linear arguments. We could have written \texttt{data MultPair a b = MkPair a b}
to the same effect.}.

\begin{code}
data MultPair a b where
    MkPair :: a %1 -> b %1 -> MultPair a b
\end{code}

The linearity annotations~\texttt{1} and \texttt{Many} are just a
specialization of the more general so-called \emph{multiplicity annotations}. A
multiplicity of \texttt{1} entails that the function argument must be consumed
once, and a function annotated with it ($\to_1$) is called a linear function
(often written with $\lolli$). A function with a multiplicity of \texttt{Many}
($\to_\omega$) is an unrestricted function, which may consume its argument 0 or more times.
Unrestricted functions are equivalent to the standard function type and, in fact,
the usual function arrow ($\to$) implicitly has multiplicity \texttt{Many}.
Multiplicities naturally allow for \emph{multiplicity polymorphism}.

Consider the functions $f$ and $g$ which take as an argument a function from
@Bool@ to @Int@. Function $f$ expects a linear function ($Bool~\to_1~Int$),
whereas $g$ expects an unrestricted function ($Bool~\to_\omega~Int$).
Function $h$ is a function from @Bool@ to @Int@ that we want to pass as an argument to both $f$
and $g$.

\begin{minipage}{0.47\textwidth}
\begin{code}
f :: (Bool %1 -> Int) -> Int
f c = c True

g :: (Bool -> Int) -> Int
g c = c False
\end{code}
\end{minipage}
\begin{minipage}{0.47\textwidth}
\begin{code}
h :: Bool %m -> Int
h x = case x of
  False -> 0
  True -> 1
\end{code}
\end{minipage}

For the application of $f$ and $g$ to $h$ to be well typed, the multiplicity of
$h$ ($\to_?$) should match the multiplicity of both $f$ ($\to_1$) and
$g$ ($\to_\omega$).
Multiplicity polymorphism allows us to use \emph{multiplicity variables} when
annotating arrows to indicate that the function can both be typed as linear and
as an unrestricted function, much the same way type variables can be used to
define polymorphic functions. Thus, we define $h$ as a multiplicity
polymorphic function ($\to_m$), making $h$ a well-typed argument to both
$f$ and $g$ ($m$ will unify with $1$ and $\omega$ at the call sites).

% \begin{itemize}
    % \item Linear Haskell definition
    % \item Consuming values precisely
    % \item Multiplicities
    % \item Multiplicity polymorphism
    % \item Files example
    % \item Ok talvez acabar abruptamente
    % \item Talvez na próxima. Que relaciona o systemFC com o calculo lambda linear
% \end{itemize}

\section{Evaluation Strategies\label{sec:background:evaluation-strategies}}

Unlike most mainstream programming languages, Haskell has so called
\emph{non-strict} evaluation semantics due to its \emph{lazy} evaluation
strategy, also known as \emph{call-by-need}~\cite{engeler_1984}.
\emph{Call-by-need} evaluation dictates that an expression is only evaluated
when it is needed (so no work is done to evaluate expressions that are unused
at runtime), and the values that are indeed evaluated are memoized and shared
across use sites. For example, the following program will only compute
|factorial 2500| if |expr| evaluates to |True|, and in
that case the work to compute it is only done once, despite being used twice:
\begin{code}
let f res = if expr then res * res else 0
in f (factorial 2500)
\end{code}
In contrast, mainstream languages commonly use an \emph{eager} evaluation
strategy called \emph{call-by-value}~\cite{engeler_1984}, in which expressions are eagerly
evaluated to a value. In the above example, under \emph{call-by-value},
|factorial 2500| would always be evaluated and passed as a value, regardless of
being used in the body. It is out of the scope of this work to discuss the
merits and trade-offs of eager vs. lazy evaluation.

% Infinite data structures,...
% A fun trick is defining lazy sorting algorithms that will only sort as many
% elements as you need from the start of the list.

A third option is the \emph{call-by-name} evaluation strategy~\cite{engeler_1984}. In
\emph{call-by-name}, expressions are only evaluated when needed, however, there
is no sharing. In the above example, it would only evaluate |factorial 2500|
\emph{twice} if |expr| were |True|. Despite being similar to
\emph{call-by-need}, in practice, language implementers prefer
\emph{call-by-need} over \emph{call-by-name} to achieve
\emph{non-strict} semantics, because the latter duplicates a lot of work, while
the former only does work once and then shares the result.


\emph{Call-by-value}, \emph{call-by-name}, and \emph{call-by-need} are the most
common evaluation strategies used to describe a language's execution model.
These execution models can be rigorously described through the operational
semantics of the language. The so-called small-step operational semantics
define the valid evaluation steps (reductions) an expression can use to evaluate to a value.
%
The operational semantics of these three evaluation models primarily differ in
how the reduction rule for function application, also known as
$\beta$-reduction, is defined:
\begin{itemize}
\item Under \emph{call-by-value}, a function application is reduced to a
\emph{value} by evaluating the function $\lambda x.~b$ and the argument $e$ to a
\emph{value} $v$, then substituting occurrences of the function argument
variable by the argument value:
\[
\begin{array}{c}
\infer{e\longrightarrow e'}{(\lambda x.~b)~e \longrightarrow (\lambda x.~b)~e'}
\qquad
(\lambda x.~b)~v \longrightarrow b[v/x]
\end{array}
\]
\item Under \emph{call-by-name}, a function application is reduced to a value
by evaluating the function to a \emph{value} (a lambda), then
substituting occurrences of the function argument variable by the whole
argument expression:
\[
\begin{array}{c}
(\lambda x.~e)~e' \longrightarrow e[e'/x]
\end{array}
\]
\item Under \emph{call-by-need}, a function application is reduced to a value
by evaluating the function to a \emph{value}, then transforming the function
application into a \textbf{let} binding:
\[
\begin{array}{c}
(\lambda x.~e)~e' \longrightarrow \llet{x = e'}{e}
\end{array}
\]
The \textbf{let} binding introduces a suspended computation known as a
\emph{thunk}, whose value is only computed when the binding is \emph{forced}.
After evaluating the expression, the binding is overwritten with the result of
the computation and subsequent uses of the binding use the
computed value without additional work.
%
Evaluation then progresses in the let body until the value of a let-bound
variable is needed, being then computed and substituted in the let body. The
call-by-need lambda calculus~\cite{cite:a-call-by-need-calculus} is, accordingly, further characterized by the following evaluation axioms:
\[
\begin{array}{l}
\llet{x = V}{C[x]} \longrightarrow \llet{x = V}{C[V]}\\
(\llet{x = L}{M})~N \longrightarrow \llet{x=L}{M~N}\\
\llet{y = (\llet{x = L}{M})}{N} \longrightarrow \llet{x=L}{\llet{y=M}{N}}
\end{array}
\]

\end{itemize}

In essence, \emph{call-by-value} gives the language \emph{strict} evaluation
semantics, where expressions are evaluated in the order they occur, s.t. using a non-terminating computation (e.g. $f(x) = f(x)$, usually
written $\bot$) in the program text will necessarily make the program not terminate
upon reaching that expression (i.e. written $g(\bot)=\bot$ for all $g$).
%
In contrast, \emph{call-by-name} and \emph{call-by-need} evaluation give the
language \emph{non-strict} semantics, where the order in which expressions are
evaluated is undefined, since they are evaluated only when needed.
%
Consequently, in non-strict semantics, using $\bot$ only results in a
non-termination if $\bot$ is evaluated, which may not be necessary for the
program to reach a result (i.e. $g(\bot) \neq \bot$, in general).

% entail non-termination -- a program does not terminate if a non-terminating
% computation is evaluated, which is not guaranteed (i.e. in \emph{call-by-name}
% and \emph{call-by-need}, $g(\bot)$ only results in non-termination ($\bot$) if
% $g$'s argument is evaluated when $g$ is executed).

\emph{Call-by-need} additionally guarantees we only do ``work'' to compute an
expression bound to a variable \emph{once}, when it is first required, and
share the result of the computation amongst subsequent occurrences of the
variable. Intuitively:
\begin{itemize}
\item When an expression is bound by a \texttt{let}, a \emph{thunk} is created,
representing the (suspended) computation that evaluates the expression to a
value

\item \emph{If} the let-bound variable is used in a computation, we must evaluate
the \emph{thunk}-suspended computation to determine the value this variable represents.

\item The \emph{thunk} is overwritten with the resulting value, s.t. subsequent
uses of the same variable now refer to the already computed value instead of
the suspended computation.
\end{itemize}
%
% done once by suspending computations into a \emph{thunk} that is overwritten
% with the value of running the suspended computation when it is \emph{forced},
% ensuring sharing of the computed result amongst subsequent uses of the same
% binding.
%
The subtleties of suspending computations (i.e.~creating \emph{thunks}) and
\emph{forcing} them under \emph{call-by-need} evaluation are especially
relevant in the context of our work regarding linearity in Core, so we review laziness in that context:

In Haskell and in its intermediate language Core, applying a function to an
expression, in general\footnote{Optimisations such as occurrence analysis, allow
us to substitute some expressions in a \emph{call-by-name}-style without
creating a let binding if the argument is only used once in the body.}, results
in a \textbf{let} binding that suspends the evaluation of the
expression/computation of the result (as per the $\beta$-reduction rule under
call-by-need).
%
Suspending a computation amounts to giving a name to the
unevaluated expression. As before, when the value associated to this name is required, then the suspended computation
is said to be \emph{forced}, a result is computed by evaluating the
expression, and the \emph{thunk} is overwritten with the result.
% The result of the computation then
% overwrites the unevaluated expression the name was associated with, and
% subsequent uses of the same name will now refer to the computed result. The
% suspended computation is called a \emph{thunk}, and
Call-by-need evaluation is traditionally modelled with a mutable heap for the
existing thunks or values they are overwritten with~\cite{}.
%
Beyond lambdas and let-bindings, Haskell and Core also feature algebraic
datatypes and case expressions to match on datatype constructors:
\begin{itemize}
\item A datatype defines a (user-defined) \emph{type} through a set of
constructors $\overline{K_i}$ that can be used to build values of the type they
define. A constructor applied to a set of argument expressions, $K~\overline{e}$, is
said to be in Weak Head Normal Form, and does not reduce any further on its own.

\item A case expression $\ccase{e_s}{\overline{\rho_i \to e_i}}$ is defined by a
scrutinee $e_s$ and a list of alternatives comprised of a pattern $\rho$
(either a wildcard $\_$, or a constructor and a set of variables to bind the
constructor arguments $K~\overline{x}$) and a right hand side expression $e_i$. Case
expressions are lazily evaluated by
  \begin{enumerate}
  \item Evaluating the scrutinee to Weak Head Normal Form, resulting in
  either a lambda expression or a constructor of arity $n$ applied to $n$
  unevaluated expressions $\overline{e_i}^n$
  \item Matching the weak head normal form of the scrutinee against the
  patterns, (possibly) substituting the pattern-bound variables of a matching
  constructor by the unevaluated arguments of a scrutinee constructor application in Weak Head Normal Form, e.g.:
  \[
  \ccase{K~\overline{e_i}^n}{K~\overline{x_i}^n \to e'} \Longrightarrow e'\overline{e_i/x_i}^n
  \]
  \end{enumerate}
\end{itemize}

Finally, briefly accounting for linearity in this context, we note that a
linear resource occurring in a suspended computation is only consumed if that
computation is executed, foreshadowing the distinction we will explore in
Section~\ref{sec:linearity-semantically} between multiple \emph{syntactic}
occurrences of a linear resource and the \emph{semantic} usages of the same
resource, where we may have multiple \emph{syntactic} occurrences of a linear
resource in suspended computations, but \emph{semantically} consume the
resource exactly once as long as we run just one of them exactly once.

\section{Core and System $F_C$\label{sec:core}}

% The section on coercions should probably mention roles, although I imagine you
% deliberately tried to avoid that. For example: p. 14 "Newtypes ... introduce a
% global type equality ... BoxI ~ Int" This is IMO quite misleading, as the
% equality is of a different nature than for GADTs and TypeFamilies.

Haskell is a large and expressive language with many syntactic constructs and
features. However, the whole of Haskell can be desugared down to a minimal,
explicitly typed, intermediate language called \textbf{Core}.
%
Desugaring allows the compiler to focus on the small desugared language rather
than on the large surface one, which can greatly simplify the subsequent
compilation passes.
%
Core is a strongly-typed, lazy, purely functional intermediate language akin to
a polymorphic lambda calculus, that GHC uses as its key intermediate
representation.
%
To illustrate the difference in complexity, in GHC's implementation of Haskell,
the abstract syntax tree is defined through dozens of datatypes and hundreds of
constructors, while the GHC's implementation of Core is defined in 3 main types
(expressions, types, and coercions) corresponding to 15 constructors~\cite{cite:ghc-source}.
%
The existence of Core and its use is a major design decision in GHC Haskell with
significant benefits which have proved themselves in the development of the
compiler.
%~\cite{,}:

\begin{itemize}
\item Core allows us to reason about the entirety of Haskell in a much smaller
functional language. Performing analysis, optimising transformations, and code
generation is done on Core, not Haskell. The implementation of these compiler passes is
significantly simplified by the minimality of Core.
 
\item Since Core is an (explicitly) typed language
(c.f.~System~F~\cite{Girard1972InterpretationFE,10.1007/3-540-06859-7_148}),
type-checking Core serves as an internal consistency check for the desugaring
and optimization passes.
%
The Core typechecker provides a verification layer for the correctness of
desugaring and optimising transformations (and their implementations) because
both desugaring and optimising transformations must produce well-typed Core.
 
\item Finally, Core's expressiveness serves as a sanity-check for
all the extensions to the source language -- if we can desugar a
feature into Core then the feature must be sound by reducibility.
Effectively, any feature added to Haskell is only syntactic sugar if it can be
desugared to Core.
\end{itemize}

The implementation of Core's typechecker differs significantly from the Haskell
typechecker because Core is explicitly typed and its type system is based on
the $System~F_C$~\cite{cite:systemfc} type system (i.e., System F extended with
a notion of type coercion), while Haskell is implicitly typed and its type
system is based on the constraint-based type inference system
$OutsideIn(X)$~\cite{cite:outsideinx}. Therefore, typechecking Core is simple,
fast, and requires no type inference, whereas Haskell's typechecker must account
for almost the entirety of Haskell's syntax,
% some features such as record updates, overloaded labels and overloaded
% rebindable syntax are desugared before the typechecker
and must perform type-inference in the presence of arbitrary-rank polymorphism,
existential types, type-level functions, and GADTs, which are known to
introduce significant challenges for type inference
algorithms~\cite{cite:outsideinx}.
%
Haskell is typechecked in addition to Core to elaborate the user program. This
might involve performing type inference to make implicit types explicit and
solving constraints to pass implicit dictionary arguments explicitly.
Furthermore, type-checking the source language allows us to provide meaningful
type errors. If Haskell wasn't typechecked and instead we only typechecked
Core, everything (e.g. all binders) would have to be explicitly typed and type
error messages would refer to the intermediate language rather than the written
program.

The Core language is based on $System~F_C$, a polymorphic lambda calculus with
explicit type-equality coercions that, like types, are erased at compile time
(i.e. types and coercions alike don't incur any cost at run-time). The
syntax of System
$F_C$~\cite{cite:systemfc} terms is given in Figure~\ref{fig:systemfc-terms}, which
corresponds exactly to the syntax of System
$F$~\cite{Girard1972InterpretationFE,10.1007/3-540-06859-7_148} with term and
(kind-annotated) type abstraction as well as term and type application,
extended with algebraic data types, let-bound
expressions, pattern matching and coercions or casts.

\begin{figure}[h]
\[
\begin{array}{lcll}
    u               & ::=  & x \mid K                           & \textrm{Variables and data constructors}\\
    e               & ::=  & u                                  & \textrm{Term atoms}\\
                    & \mid & \Lambda a{:}\kappa.~e~\mid~e~\varphi  & \textrm{Type abstraction/application}\\
                    & \mid & \lambda x{:}\sigma.~e~\mid~e_1~e_2 & \textrm{Term abstraction/application}\\
                    & \mid & \llet{x{:}\sigma = e_1}{e_2}       & \\
                    & \mid & \ccase{e_1}{\overline{p\to e_2}}   & \\
                    & \mid & e \blacktriangleright \gamma       & \textrm{Cast} \\
                    &      &                                    & \\
    p               & ::= & K~\overline{b{:}\kappa}~\overline{x{:}\sigma} & \textrm{Pattern}
\end{array}
\]
\caption{System $F_C$'s Terms\label{fig:systemfc-terms}}
\end{figure}

Explicit type-equality coercions (or simply coercions), written
$\sigma_1 \sim \sigma_2$, serve as evidence of
equality between two types $\sigma_1$ and $\sigma_2$. A coercion $\sigma_1\sim\sigma_2$ can be used to safely
\emph{cast} an expression $e$ of type $\sigma_1$ to type $\sigma_2$, where
casting $e$ to $\sigma_2$ using $\sigma_1\sim\sigma_2$ is written
$e\blacktriangleright\sigma_1\sim\sigma_2$. The syntax of \emph{coercions} is
given by Figure~\ref{fig:systemfc-types} and describes how coercions can be
constructed to justify new equalities between types (e.g. using symmetry and
transitivity). For example, given $\tau\sim\sigma$, the coercion
$\textbf{sym}~(\tau\sim\sigma)$ denotes a type-equality coercion from $\sigma$
to $\tau$ using the axiom of symmetry of equality. Through it, the expression
$e{:}\sigma$ can be cast to $e{:}\tau$, i.e.
$(e{:}\sigma\blacktriangleright\textbf{sym}~\tau\sim\sigma) : \tau$.

\begin{figure}[h]
\[
\begin{array}{lcll}
  \sigma,\tau & ::= & d \mid \tau_1~\tau_2 \mid S_n~\overline{\tau}^n \mid \forall a{:}\kappa. \tau & \textrm{Types} \\
  \gamma,\delta & ::= & g \mid \tau \mid \gamma_1~\gamma_2 \mid S_n~\overline{\gamma}^n \mid \forall a{:}\kappa. \gamma & \textrm{Coercions} \\
                & \mid & \textbf{sym}~\gamma \mid \gamma_1\circ\gamma_2 \mid \gamma @@ \sigma \mid \textbf{left}~\gamma \mid \textbf{right}~\gamma \\
  \varphi & ::= & \tau \mid \gamma & \textrm{Types and Coercions}
\end{array}
\]
\caption{System $F_C$'s Types and Coercions\label{fig:systemfc-types}}
\end{figure}


$System~F_C$'s coercions are key in desugaring  advanced type-level Haskell features such as GADTs, type families and newtypes~\cite{cite:systemfc}. In
short, these three features are desugared as follows:
\begin{itemize}
  \item GADTs local equality constraints are desugared into explicit type-equality
  evidence that are pattern matched on and used to cast the branch alternative's
  type to the return type.

  \item Newtypes such as @newtype BoxI = BoxI Int@ introduce a global
  type-equality $\texttt{BoxI}$ $\sim \texttt{Int}$ and construction and
  deconstruction of said newtype are desugared into casts.

  \item Type family instances such as @type instance F Int = Bool@ introduce a
  global coercion $\texttt{F~Int}\sim\texttt{Bool}$ which can be used to cast
  expressions of type $\texttt{F~Int}$ to $\texttt{Bool}$.
\end{itemize}

Core further extends $System~F_C$ with \emph{jumps} and \emph{join
points}~\cite{maurer2017compiling}, allowing new optimizations to be performed
which ultimately result in efficient code using labels and jumps, and
with a construct used for internal notes such as profiling information.
% DONE: \todo{We could mention Sequent Core as the origin of jumps and joins here, or simply cite it}

% $System~F_C$ is expressive enough as a target for Haskell

In the context of Linear Haskell, and recalling that Haskell is fully
desugared into Core / System~$F_C$ as part of its validation and
compilation strategy, we highlight the inherent incompatibility of
linearity with Core / System~$F_C$ as a current flaw in GHC that
invalidates all the benefits of Core wrt linearity.  Thus, we must
extend System $F_C$ (and, therefore, Core) with linearity in order to
adequately validate the desugaring and optimising transformations as
linearity preserving, ensuring we can reason about Linear Haskell in
its Core representation.

% \begin{itemize}
% \item Referencia figura, as can be seen in bla, is a lambda calculus type system with coercions
% \item Figura com syntax do system FC
% \item Coercions
% \item Coercions são para local equalities, type families, func deps, newtypes e etc, tornam possível fazer o desugar das features mais complicadas
% \item No contexto dos linear types ...  Revisitando a idea de desugar para
%        core... system fc...  Esta linguagem as is não suporta linearidade e não
%        permite seguir esta filosofia de "desugar to core" por que Core não suporta,
%        fundamentalmente incompatível com linearidade, e por isso é preciso integrar
%        linearidade no systemFC (consequently no Core)
%\end{itemize}

% \begin{itemize}
    % \item What is Core (IR) e as particularidades
    % \item Em cima do SystemFC
    % \item Optimizações feitas no Core
    % \item Base SystemFC tem de ser "merged" com o linear lambda calculus
    % \item Ou porque é que é importante o Core ter linearidade também/a que nível foi introduzido
    % \item Falar das coercions em especifico
    % \item E das local equalities que são implicitas no front end
% \end{itemize}

\section{GHC Pipeline\label{sec:ghcpipeline}}

The GHC compiler processes Haskell source files in a series of phases that feed
each other in a pipeline fashion, each transforming their input before passing
it on to the next stage.
%
This pipeline is % (Figure~\ref{fig:ghc-pipeline})
crucial in the overall design of GHC. We now give a high-level
overview of the phases.

\subsection{Haskell to Core}

\parawith{Parser.} The Haskell source files are first processed by the lexer
and the parser. The lexer transforms the input file into a sequence of valid
Haskell tokens. The parser processes the tokens to create an abstract syntax
tree representing the original code, as long as the input is a syntactically
valid Haskell program.

\parawith{Renamer.} The renamer's main tasks are to resolve names to fully
qualified names, resolve name shadowing, and resolve namespaces (such as the
types and terms namespaces), taking into consideration both existing
identifiers in the module being compiled and identifiers exported by other
modules. Additionally, name ambiguity, variables out of scope, unused bindings
or imports, etc., are checked and reported as errors or warnings.

\parawith{Type-checker.} With the abstract syntax tree validated by
the renamer and with the names fully qualified, the Haskell program is
type-checked before being desugared into Core.  Type-checking the Haskell
program guarantees that the program is well-typed. Otherwise, type-checking
fails with an error reporting where in the source typing failed.
%
Furthermore, every identifier in the program is annotated with its type.
Haskell is an implicitly typed language and, as such, type-inference must be
performed to type-check programs. During type inference, every identifier is
typed and we can use its type to decorate said identifier in the abstract
syntax tree produced by the type-checker. First, annotating identifiers is
\emph{required} to desugar Haskell into Core because Core is explicitly typed -- to
construct a Core abstract syntax tree the types are indispensable (i.e.
we cannot construct a Core expression without explicit types). Secondly, names
annotated with their types are useful for tools manipulating Haskell, e.g.
for an IDE to report the type of an identifier.

\parawith{Desugaring.} The type-checked Haskell abstract syntax tree is then
transformed into Core by the desugarer. We've discussed in
Section~\ref{sec:core} the relationship between Haskell and Core in detail, so we
refrain from repeating it here. It suffices to say that the desugarer
transforms the large Haskell language into the small Core language by
simplifying all syntactic constructs to their equivalent Core form (e.g.  @newtype@
constructors are transformed into coercions).

\subsection{Core-To-Core Transformations\label{sec:core-to-core-transformations}}

% TODO: Rewrite rules which also operate on Core
% TODO: Split worker/wrapper into its own section?

The Core-to-Core transformations are the most important set of
optimising transformations that GHC performs during compilation. By design, the
frontend of the pipeline (parsing, renaming, typechecking and desugaring) does
not include any optimizations -- all optimizations are done in Core.
The transformational approach focused on Core, known as \emph{compilation by
  transformation}, allows transformations to be both modular and simple.
Each transformation focuses on optimising a specific set of
constructs, where applying a transformation often exposes opportunities for
other transformations to fire. Since transformations are modular, they
can be chained and iterated in order to maximize the optimization potential (as
shown in Figure~\ref{fig:eg:transformations}).


% I know this paragraph is useless :)
However, due to the destructive nature of transformations (i.e. applying a
transformation is not reversible), the order in which transformations are
applied determines how well the resulting program is optimised.  As such,
certain orderings of optimizations can hide optimization opportunities and
block them from firing. This phase-ordering problem is present in most
optimising compilers.

% Techniques such as
% equality saturation~\cite{} bypass the phase-ordering problem because all
% optimising transformations are applied non-destructively; however, it's a much
% more expensive technique that has not been .
%
% transformation based approach to optimization allows each producing a Core
% program fed to the next optimising transformation.


Foreshadowing the fact that Core is the main object of our study, we want to type-check
linearity in Core before \emph{and} after each optimising transformation is
applied (Section~\ref{sec:core}).
%
In light of it, we describe below some of the individual Core-to-Core
transformations, using $\Longrightarrow$ to denote a program transformation. In
the literature, the first set of Core-to-Core optimizations was described
in~\cite{santos1995compilation,peytonjones1997a}. These were subsequently
refined and
expanded~\cite{peytonjones2002secrets,baker-finch2004constructed,maurer2017compiling,Breitner2016_1000054251,sergey_vytiniotis_jones_breitner_2017}.
In Figure~\ref{fig:eg:transformations} we present an example that is optimised
by multiple transformations to highlight how the compilation by transformation
process produces performant programs.

% \begin{figure}[h]
% \begin{tikzpicture}
% %Define the function structure
% \tikzset{
%   grow'=right,level distance=25mm, sibling distance =3.5mm,
%   execute at begin node=\strut,
%   every tree node/.style={
% 			draw,
% 			rounded corners,
% 			anchor = west,
% 			minimum width=20mm,
% 			text width=18mm,
% 			align=center,
% 			font = {\scriptsize}},
%          edge from parent/.style={draw, edge from parent fork right}
% }
% %Draw the function structure (top to bottom)
% %distance from root: width of tree
% \begin{scope}[frontier/.style={distance from root=75mm}]
% \Tree
% [.{Overall-\\ Function}
% 		[.{Main-\\ Function A}
% 			[.{Sub-Function\\ A}
% 			\node(f1){Function A};
% 			\node(f2){Function B};
% 			\node(f3){Function C};
% 			]
% 			\node(f4){Function D};
% 		]
% 		[.{Main-\\ Function B}
% 			[.{Sub-Function\\ B}
% 				\node(f5){Function E};
% 				\node(f6){Function F};
% 				\node(f7){Function G};
% 			]
% 			\node(f8){Function H};
% 		]
% 		\node(f9){Function I};
% ]
% \end{scope}
% %Define the product structure
% \tikzset{grow'=left,
% 		sibling distance =3.85mm,
%        edge from parent/.style={
%          draw, edge from parent fork left}
% }
% %Draw the product structure (bottom up)
% %distance from root: width of tree
% %xshift/yshift: Shiftoption of right tree
% \begin{scope}[
% 	frontier/.style={distance from root=75mm},
% 	xshift=190mm,
% 	yshift=4.9mm]
% \Tree
% [.{Product}
% 		\node(p8){Part H};
% 		[.{Module A}
% 			[.{Component B}
% 				\node(p7){Part G};
% 				\node(p6){Part F};
% 				\node(p5){Part E};
% 			]
% 			\node(p4){{Part D}};
% 		]
% 		[.{Module B}
% 			[.{Component A}
% 				\node(p3){Part C};
% 				\node(p2){Part B};
% 				\node(p1){Part A};
% 			]
% 		]
% ]
% \end{scope}
% %Draw the lines between function and product side
%   \draw [thick, >=stealth, dashed]
%         (f1.east)--(p1.west)
%         (f2.east)--(p2.west)
%         (f3.east)--(p3.west)
%         (f3.east)--(p1.west)
%         (f4.east)--(p4.west)
%         (f5.east)--(p5.west)
%         (f6.east)--(p6.west)
%         (f7.east)--(p7.west)
%         (f7.east)--(p6.west)
%         (f8.east)--(p4.west)
%         (f8.east)--(p5.west)
%         (f8.east)--(p8.west)
%         (f9.east)--(p7.west);
% %Draw the headlines
% \begin{scope}[every node/.style = {rounded corners, font = {\normalsize\bfseries}}]
% \node at (5,5) [] {function structure};
% \node at (16,5) [rounded corners] {product structure};
% \end{scope}
% \end{tikzpicture}
% \end{figure}

% Ideia de que há uma transformação .... pipeline... e depois há muitas
% transformações feitas internamente dentro do Core,STG,Cmm,LLVM e que o meu foco
% fundamental é as trasnformações CoreToCore
% 
% Typechecekr sobre o Haskell, é produzido Core com termos anotados
% explicitamente que saem do typechecker do Haskell e depois gera-se código que
% primeiro é preciso optimizar core...
% 
% The architecture of GHC
% Both typecheckers, the backends Core is transformed into, and \textbf{\emph{all
% core transformations}}.

%\begin{itemize}
    % \item Parser to Rename to Typechecker to Desugar
    % \item Core2Core transformations
    % \item GHC unique em haver tantas transformações sempre sobre a mesma intermediate
    %    representation como input e output
%\end{itemize}

% Previous itemize. Talvez ainda tenha de ter secções sobre os últimos dois
% pontos
% \begin{itemize}
%     \item Linear types
%     \item Linear Haskell
%     \item Core
%     \item Sistemas de inferência
%     \item GADTs e Coercions
% \end{itemize}

% like inlining, its inverse (CSE), beta-reduction, lambda-lifting,
% eta-reduction/eta-expansion, binder-swap, case-of-case,
% case-of-know-constructor, float-out, float-in, worker/wrapper split (this one
% is big, in comparison), etc…

\parawith{Inlining.} Inlining is an optimization common to all compilers, but
especially important in functional languages~\cite{peytonjones1997a}. Given
Haskell's pure and lazy semantics, inlining can be employed in Haskell to a much
larger extent because we needn't worry about evaluation order or side effects,
contrary to most imperative and strict languages. \emph{Inlining} consists of
replacing an occurrence of a let-bound variable by its right-hand side:
\[
\llet{x = e}{e'}~\Longrightarrow~\llet{x = e}{e'[e/x]}
\]
Effective inlining is crucial to optimization because, by bringing the
definition of a variable to the context in which it is used, many other local
optimizations are unlocked. The work~\cite{peytonjones2002secrets} further
discusses the intricacies of inlining and provides algorithms used for inlining
in GHC.

\parawith{$\beta$-reduction.} $\beta$-reduction is an optimization that
consists of reducing an application of a term $\lambda$-abstraction or
type-level $\Lambda$-abstraction (Figure~\ref{fig:systemfc-terms}) by replacing
the $\lambda$-bound variable with the argument the function is applied to:
\[
(\lambda x{:}\tau.~e)~y~\Longrightarrow~e[y/x]
\qquad
(\Lambda a{:}\kappa.~e)~\varphi~\Longrightarrow~e[\varphi/a]
\]
If the $\lambda$-bound variable is used more than once in the body of the
$\lambda$-abstraction we must be careful not to duplicate work, and we can
let-bound the argument, while still removing the $\lambda$-abstraction, to avoid
doing so:
\[
(\lambda x{:}\tau.~e)~y~\Longrightarrow~\llet{x = y}{e}
\]
$\beta$-reduction is always a good optimization because it effectively evaluates
the application at compile-time (reducing heap allocations and execution time)
and unlocks other transformations.

\parawith{Case-of-known-constructor.} If a \texttt{case} expression is
scrutinizing a known constructor $K~\overline{x{:}\sigma}$, we can simplify the
case expression to the branch it would enter, substituting the pattern-bound
variables by the known constructor arguments ($\overline{x{:}\sigma}$):
\[
\begin{array}{lcl}
\textbf{case}~K~v_1~\dots~v_n~\textbf{of}\\
~~K~x_1~\dots~x_n \to e \\
~~\dots
\end{array}
\Longrightarrow
e[v_i/x_i]_{i=1}^n
\]
Case-of-known-constructor is an optimization mostly unlocked by other
optimizations such as inlining and $\beta$-reduction, more so than by code
written as-is by the programmer. As $\beta$-reduction, this optimization is also
always good -- it eliminates evaluations whose result is known at compile time
and further unblocks for other transformations.


% não gosto da frase abaixo
\parawith{Let-floating.} A let-binding in Core entails performing
\emph{heap-allocation}, therefore, let-related transformations directly impact
the performance of Haskell programs. In particular, let-floating
transformations are concerned with best the position of let-bindings in a
program in order to improve efficiency. Let-floating is an important group of
transformations for non-strict (lazy) languages described in detail
by~\cite{cite:let-floating}. We distinguish three let-floating transformations:
\begin{itemize}
  \item \emph{Float-in} consists of moving a let-binding as far \emph{inwards}
  as possible. For example, it could be moving a let-binding outside of a case
  expression into the branch alternative that uses the let-bound variable:
  \[
  \begin{array}{l}
    \llet{x = y+1\\}{\ccase{z}{\\\ ~[] \to x*x \\~~(p:ps) \to 1}}
  \end{array}
  \Longrightarrow
  \begin{array}{l}
    \ccase{z}{\\\ [] \to \llet{x = y+1}{x*x} \\~(p:ps) \to 1}
  \end{array}
  \]
  This can improve performance by not performing let-bindings (e.g. if the
  branch the let was moved into is never executed); improving strictness
  analysis; and further unlocking other optimizations such as
  ~\cite{cite:let-floating}. However, care must be taken when floating a
  let-binding inside a $\lambda$-abstraction because every time that
  abstraction is applied the value (or thunk) of the binding will be allocated
  in the heap.

  \item \emph{Full laziness} transformation, also known as \emph{float-out},
  consists of moving let-bindings outside of enclosing $\lambda$-abstractions.
  The warning above regarding $\lambda$-abstractions recomputing the binding
  every time they are applied is valid even if bindings are not purposefully
  pushed inwards. In such a situation, floating the let binding out of the
  enclosing lambda can make it readily available across applications of said
  lambda.
  \[
  \begin{array}{l}
  \lambda y.~\llet{x = e}{e'}
  \end{array}
  \Longrightarrow
  \begin{array}{l}
  \llet{x = e}{\lambda y.~e'}
  \end{array}
  \]

  \item The \emph{local transformations} are the third type of let-floating
  optimizations. In this context, the local transformations are local rewrites
  that improve the placement of bindings. There are three local
  transformations:
  \[
  \begin{array}{llcl}
  1. & (\llet{v = e}{b})~a              & \Longrightarrow & \llet{v = e}{b~a} \\
  2. & \ccase{(\llet{v = e}{b})}{\dots} & \Longrightarrow & \llet{v = e}{\ccase{b}{\dots}}\\
  3. & \llet{x = (\llet{v = e}{b})}{c}  & \Longrightarrow & \llet{v = e}{\llet{x = b}{c}} \\
  \end{array}
  \]
  These transformations do not change the number of allocations but potentially
  create opportunities for other optimizations to fire, such as expose a lambda
  abstraction~\cite{cite:let-floating}.
\end{itemize}

\parawith{$\eta$-expansion and $\eta$-reduction.} $\eta$-expansion is a transformation
that expands a function expression $f$ to $(\lambda x. f~x)$, where $x$ is not
free in $f$. This transformation can improve efficiency because it can fully
apply functions which would previously be partially applied by using the
variable bound to the expanded $\lambda$. A partially applied function is often
more costly than a fully saturated one because it entails a heap allocation for
the function closure, while a fully saturated one equates to a function call.
$\eta$-reduction is the inverse transformation to $\eta$-expansion, i.e., a
$\lambda$-abstraction $(\lambda x.  f~x)$ can be $\eta$-reduced to simply~$f$.

\parawith{Case-of-case.} The case-of-case transformation fires when a case
expression is scrutinizing another case expression. In this situation, the
transformation duplicates the outermost case into each of the inner case
branches:
\[
\begin{array}{lcl}
\ccase{\left( \begin{array}{c}\ccase{e_c}{\\~alt_{c_1} \to e_{c_1}
                                          \\~\dots
                                          \\~alt_{c_n} \to e_{c_n}}\end{array} \right)}{\\~alt_1 \to e_1
                                                                                        \\~\dots
                                                                                        \\~alt_n \to e_n}
\end{array}
\Longrightarrow
\begin{array}{lcl}
\ccase{e_c}{\\~alt_{c_1} \to \left( \begin{array}{c}\ccase{e_{c_1}}{\\~alt_1 \to e_1
                                                         \\~\dots
                                                         \\~alt_n \to e_n}\end{array} \right)
            \\~\dots
            \\~alt_{c_n} \to \left( \begin{array}{c}\ccase{e_{c_n}}{\\~alt_1 \to e_1
                                                         \\~\dots
                                                         \\~alt_n \to e_n}\end{array} \right)}
\end{array}
\]
This transformation exposes other optimizations, e.g., if $e_{c_n}$ is a known
constructor we can readily apply the \emph{case-of-known-constructor}
optimization. However,
this transformation also potentially introduces significant code
duplication. To this effect,
we apply a transformation that creates \emph{join points} (i.e.,~shared bindings outside
the case expressions that are used in the branch alternatives) that are
compiled to efficient code using labels and jumps.

\parawith{Common sub-expression elimination.}
%
Common sub-expression elimination (CSE) is a transformation that is
effectively inverse to \emph{inlining}.
This transformation factors out expensive expressions into a
shared binding. In practice, lazy functional languages don't benefit nearly as
much as strict imperative languages from CSE and, thus, it isn't very important
in GHC~\cite{10.1007/BFb0055424}.

\parawith{Static argument and lambda lifting.} \emph{Lambda lifting} is a
transformation that abstracts over free variables in functions by making them
$\lambda$-bound
arguments~\cite{10.1007/3-540-15975-4_37,santos1995compilation}. This allows
functions to be ``lifted'' to the top-level of the program (because they no
longer have free variables). Lambda lifting may unlock inlining opportunities
and allocate less function closures, since the definition is then created only
once at the top-level and shared across uses.
%
The \emph{static argument} transformation identifies function arguments which
are \emph{static} across calls, and eliminates said \emph{static argument} to
avoid passing the same fixed value as an argument in every function call, which
is especially significant in recursive functions. To this effect, the
\emph{static argument} is bound outside of the function definition and becomes
a free variable in its body. It can be thought of as the transformation inverse
to \emph{lambda lifting}.

\parawith{Strictness analysis and worker/wrapper split.} The strictness
analysis, in lazy programming languages, identifies functions that always
evaluate their arguments, i.e.  functions with (morally) \emph{strict
arguments}. Arguments passed to functions that necessarily evaluate them can be
evaluated before the call and therefore avoid some heap allocations. The
strictness analysis may be used to apply the worker/wrapper split
transformation~\cite{peytonjones1993measuring}. This transformation creates two
functions from an original one: a worker and a wrapper. The worker receives
unboxed values~\cite{10.1007/3540543961_30} as arguments, while the wrapper
receives boxed values, unwraps them, and simply calls the worker function
(hence the wrapper being named as such). This allows the worker to be called in
expressions other than the wrapper, saving allocations and being possibly much
faster, especially if the worker recursively ends up calling itself rather than
the wrapper.

% Leave it... \todo[inline]{Add examples/definitions to the three previous transformations}

% DONE \todo[inline]{Add a paragraph about the binder swap, and another about the
% reverse binder swap, possibly foreshadowing how it is important in our study as
% something that is only linearity preserving because of the way other
% optimizations are defined.}

\parawith{Binder-swap.} The binder swap transformation applies to a case
expression whose scrutinee is a variable $x$, and consists of swapping the case
binder $z$ for $x$ in all case alternatives:
\[
\ccase{x}{z~\{\overline{\rho_i\to e_i}\}} \Longrightarrow \ccase{x}{z~\{\overline{\rho_i\to e_i[z/x]}\}}
\]
By removing occurrences of $x$ in the case alternatives we might end up with
the case scrutinee being the only occurrence of $x$, which allows us to inline
$x$ and possibly save an allocation, for example:
\[
\begin{array}{l}
\llet{x = factorial~y}{\ccase{x}{b~\{ I\#~v \to \dots x \dots \}}}\\
\Longrightarrow_{Binder~swap}\\
\llet{x = factorial~y}{\ccase{x}{b~\{ I\#~v \to \dots b \dots \}}}\\
\Longrightarrow_{Inlining}\\
\ccase{factorial~y}{b~\{ I\#~v \to \dots b \dots \}}\\
\end{array}
\]
\parawith{Reverse binder-swap.} The reverse binder swap is (unsurprisingly) the
reverse of the binder swap transformation. For a case whose scrutinee is a
variable $x$, reverse binder swaps occurrences of the case binder $z$ by the
variable $x$:
\[
\ccase{x}{z~\{\overline{\rho_i\to e_i}\}} \Longrightarrow \ccase{x}{z~\{\overline{\rho_i\to e_i[x/z]}\}}
\]
It is not entirely obvious why this might optimise a program, however, $z$ is
bound in the case alternative, so expressions involving $z$ may not be floated
out of the case alternative. If $z$ is substituted by $x$, which isn't bound to
the case, we might float out an expensive operation out of the case
alternatives and, for example, out of a loop:
\[
\begin{array}{l}
\lletrec{go~y = \ccase{x}{z~\{(a,b) \to \dots (expensive~z) \dots\}}}{\dots go \dots}\\
\Longrightarrow_{Reverse~binder~swap}\\
\lletrec{go~y = \ccase{x}{z~\{(a,b) \to \dots (expensive~x) \dots\}}}{\dots go \dots}\\
\Longrightarrow_{Float~out}\\
\llet{t = expensive~x}{\lletrec{go~y = \ccase{x}{z~\{(a,b) \to \dots t \dots\}}}{\dots go \dots}}
\end{array}
\]
In this example, $expensive~x$ is now computed once, instead of once per loop
iteration.
% (suggested by Simon P. Jones)


\begin{figure}[ht]
\[
\begin{array}{lc}
\begin{array}{l}\textrm{if}~(not~x)~\textrm{then}~e_1~\textrm{else}~e_2\end{array} & \overset{Desugar}{\Longrightarrow}\\
\\
\begin{array}{l}\ccase{not~x}{\\~~\textrm{True}\to e_1\\~~\textrm{False}\to e_2}\end{array} & \overset{Inline~not}{\Longrightarrow} \\
\\
\begin{array}{l}\ccase{\left(\begin{array}{l}\lambda y. \ccase{y}{\\~\textrm{True}\to\textrm{False}\\~\textrm{False}\to\textrm{True}}\end{array}\right)~x}{\\~~\textrm{True}\to e_1\\~~\textrm{False}\to e_2}\end{array} & \overset{\beta-reduction}{\Longrightarrow} \\
\\
\begin{array}{l}\ccase{\left(\begin{array}{l}\ccase{x}{\\~\textrm{True}\to\textrm{False}\\~\textrm{False}\to\textrm{True}}\end{array}\right)}{\\~~\textrm{True}\to e_1\\~~\textrm{False}\to e_2}\end{array} & \overset{Case-of-case}{\Longrightarrow} \\
\\
\begin{array}{l}\ccase{x}{\\~~\textrm{True}\to\left(\begin{array}{l}\ccase{\textrm{False}}{\\~\textrm{True}\to e_1\\~\textrm{False}\to e_2}\end{array}\right)\\~~\textrm{False}\to\left(\begin{array}{l}\ccase{\textrm{True}}{\\~\textrm{True}\to e_1\\~\textrm{False}\to e_2}\end{array}\right)}\end{array} & \overset{Case-of-known-constructor}{\Longrightarrow} \\
\\
\begin{array}{l}\ccase{x}{\\~~\textrm{True}\to e_2\\~~\textrm{False}\to e_1}\end{array} & \square \\
\end{array}
\]
\caption{Example sequence of transformations}
\label{fig:eg:transformations}
\end{figure}

\subsection{Code Generation}

The code generation needn't be changed to account for the work we will do in
the context of this thesis, so we only briefly describe it.

After the core-to-core pipeline is run on the Core program and produces
optimised Core, the program is translated down to the Spineless Tagless
G-Machine (STG) language~\cite{jones_1992}. STG language is a small functional
language that serves as the abstract machine code for the STG abstract machine
that ultimately defines the evaluation model and compilation of Haskell through
operational semantics.

From the abstract state machine, we generate C\texttt{--} (read C minus minus), a C-like language designed
for native code generation, which is finally passed as input to one of the code
generation backends\footnote{GHC is not \emph{yet} runtime retargetable, i.e.
to use a particular native code generation backend the compiler must be built
targetting it.}, such as LLVM, x86 and x64, or (recently) JavaScript and WebAssembly.

