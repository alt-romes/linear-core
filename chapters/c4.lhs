%include polycode.fmt
\input{proof}
\renewcommand{\llet}[2]{\mathbf{let}~#1~\mathbf{in}~#2}
\renewcommand{\lletrec}[2]{\mathbf{let~rec}~#1~\mathbf{in}~#2}
\renewcommand{\ccase}[2]{\mathbf{case}~#1~\mathbf{of}~#2}
\newcommand{\judgment}[1]{
    \begin{tabular}{V{2.7}cV{2.7}}
    \hlineB{2.7}
    $#1$\\
    \hlineB{2.7}
    \end{tabular}
}
\newcommand{\datatype}[2]{
  \mathbf{data}~#1~\mathbf{where}~#2
}

\chapter{Linear Core*}

\begin{figure}[h]
\begin{framed}
\[
\begin{array}{l}
%
\textbf{Types} \\
\begin{array}{lcll}
    \varphi,\sigma & ::= & T~\overline{p} & \textrm{Datatype} \\
                   & \mid & \varphi \to_\pi \sigma & \textrm{Function with multiplicity}\\
                   & \mid & \forall p.~\varphi & \textrm{Multiplicity universal scheme}\\
                   % TODO: Eventually Coercions
\end{array}\\\\
%
\textbf{Terms}\\
\begin{array}{lcll}
    u               & ::=  & x,y,z \mid K                           & \textrm{Variables and data constructors}\\
    e               & ::=  & u                                  & \textrm{Term atoms}\\
                    & \mid & \Lambda p.~e~\mid~e~\pi  & \textrm{Multiplicity abstraction/application}\\
                    & \mid & \lambda x{:}_\pi\sigma.~e~\mid~e_1~e_2 & \textrm{Term abstraction/application}\\
                    & \mid & \llet{x{:}_\Delta\sigma = e_1}{e_2}       & \textrm{Let} \\
                    & \mid & \lletrec{\overline{x{:}_\Delta\sigma = e_1}}{e_2}  & \textrm{Recursive Let} \\
                    & \mid & \ccase{e_1}{z{:}_{\overline{\Delta}}~\{\overline{\rho\to e_2}\}}   & \textrm{Case} \\
                    &      &                                    & \\
%    p               & ::= & K~\overline{b{:}\kappa}~\overline{x{:}\sigma} & \textrm{Pattern} \\
    \rho            & ::= & K~\overline{x{:}_\pi\sigma} \mid \_ & \textrm{Pattern and wildcard} \\
% Currently we don't care about the existential multiplicity variables, but later on we might
\end{array}\\\\
%
\textbf{Environments}\\
\begin{array}{lcll}
  \Gamma & ::= & \cdot & \textrm{Empty environment} \\
         & \mid & \Gamma,x{:}_\pi\sigma & \textrm{Lambda bound variable} \\
         & \mid & \Gamma,x{:}_\Delta\sigma & \textrm{Let(rec) bound variable}\\
         % & \mid & \Gamma,x{:}_{\overline{\Delta}}\sigma & \textrm{Case bound variables} -- NOPE
         & \mid & \Gamma,K{:}\sigma & \textrm{Data constructor}\\
         & \mid & \Gamma,p & \textrm{Multiplicity variable}\\
\end{array}\\\\
%
\textbf{Multiplicities}\\
\begin{array}{lcll}
  \pi, \mu & ::= & 1 \mid \omega \mid p \mid \pi + \mu \mid \pi \cdot \mu\\
% We don't use + and cdot yet, but we will
\end{array}\\\\
%
\textbf{Usage Environments}\\
\begin{array}{lcl}
  \Delta & ::= & \cdot \mid \Delta, x{:}_\pi\sigma \mid \Delta+\Delta' \mid \pi\Delta\\
\end{array}\\\\
%
\textbf{Declarations}\\
\begin{array}{lcl}
  pgm & ::= & \overline{decl}; e \\
  decl & ::= & \datatype{T~\overline{p}}{\overline{K:\overline{\sigma \to_\pi}~T~\overline{p}}}
\end{array}
%
\end{array}
\]
\end{framed}
\caption{Linear Core* Syntax}
\label{linear-core-syntax}
\end{figure}



\begin{figure}[h]
\begin{framed}
\small
\[
\begin{array}{c}
    \judgment{\Gamma \vdash e : \sigma}
\\[1em]
    \infer*[right=($Weaken_\omega$)]
    {\Gamma \vdash e : \varphi}
    {\Gamma , x{:}_\omega \sigma \vdash e : \varphi}
\qquad
    \infer*[right=($Weaken_\Delta$)]
    {\Gamma \vdash e : \varphi}
    {\Gamma , x{:}_\Delta \sigma \vdash e : \varphi}
\\[1em]
    \infer*[right=($Contract_\omega$)]
    {\Gamma , x{:}_\omega \sigma, x{:}_\omega \sigma \vdash e : \varphi}
    {\Gamma , x{:}_\omega \sigma \vdash e : \varphi}
\qquad
    \infer*[right=($Contract_\Delta$)]
    {\Gamma , x{:}_\Delta \sigma, x{:}_\Delta \sigma \vdash e : \varphi}
    {\Gamma , x{:}_\Delta \sigma \vdash e : \varphi}
\\[1em]
    \infer*[right=($Var_1$)]
    { }
    {\cdot, x{:}_1 \sigma \vdash x : \sigma}
\qquad
    \infer*[right=($Var_\omega$)]
    { \forall y{:}_\pi\varphi \in \Gamma .~\pi \neq 1 }
    {\Gamma, x{:}_\omega \sigma \vdash x : \sigma}
\qquad
    \infer*[right=($Var_\Delta$)]
    { \Delta\!\upharpoonright_1 = \Gamma }
    {\Gamma , x{:}_\Delta \sigma \vdash x : \sigma}
\\[1em]
    \infer*[right=($\Lambda I$)]
    {\Gamma, p \vdash e : \sigma \and p \notin \Gamma}
    {\Gamma \vdash \Lambda p.~e : \forall p. \sigma}
\qquad
    \infer*[right=($\Lambda E$)]
    {\Gamma \vdash e : \forall p.~\sigma \and \Gamma \vdash_{mult} \pi}
    {\Gamma \vdash e~\pi : \sigma[\pi/p]} % ROMES:TODO: Subsittution the other way around?
\\[1em]
    \infer*[right=($\lambda I$)]
    {\Gamma, x{:}_\pi\sigma_1 \vdash e : \sigma_2}
    {\Gamma \vdash \lambda x{:}_\pi\sigma_1.~e : \sigma_1 \to_\pi \sigma_2}
\qquad
    \infer*[right=($\lambda E$)]
    {\Gamma \vdash e_1 : \sigma_2 \to_\pi \sigma_1 \and \Gamma' \vdash e_2 : \sigma_2}
    {\Gamma,\Gamma' \vdash e_1~e_2 : \sigma_1}
\\[1em]
    \infer*[right=($Let$)]
    {\Gamma, x{:}_\Delta\sigma_1 \vdash e_2 : \sigma_2 \and \Delta \vdash e_1 :
    \sigma_1 \and \Delta \subseteq \Gamma}
    {\Gamma \vdash \llet{x{:}_\Delta\sigma_1 = e_1}{e_2} : \sigma_2}
    % em alternativa a isto que está errado (separar o \Gamma em \Gamma, \Delta)
    % \infer*[right=($Let_{Wrong}$)]
    % {\Gamma, x{:}_\Delta\sigma_1 \vdash e : \sigma_2 \and \Delta \vdash u : \sigma_1}
    % {\Gamma,\Delta \vdash \llet{x{:}_\Delta\sigma_1 = u}{e} : \sigma_2}
\\[1em]
    % \infer*[right=($LetRec$)]
    % {\Gamma, \overline{x_n{:}_{\Delta_n}\sigma_n } \vdash e : \varphi \and \overline{\Delta_n \vdash u_n : \sigma_n}}
    % {\Gamma \vdash \lletrec{\overline{x_n{:}_{\Delta_n}\sigma_n = u_n}}{e} : \varphi}
    % ROMES:TODO:FIXME:(later...what???)
    \infer*[right=($LetRec$)]
    {\Gamma, \overline{x{:}_{\Delta}\sigma} \vdash e : \varphi \and
    \overline{\Delta, \overline{x{:}_{\Delta}\sigma} \vdash e' : \sigma} \and
    \overline{\Delta \subseteq \Gamma}}
    {\Gamma \vdash \lletrec{\overline{x{:}_{\Delta}\sigma = e'}}{e} : \varphi}
\\[1em]
    \infer*[right=($Case$)]
    { \Gamma \vdash e_1 : \sigma \and \overline{\Gamma', z{:}_{\Delta_i}\sigma \vdash_{alt} \rho_i \to e_i : \sigma \Rightarrow \varphi} }
    {\Gamma, \Gamma' \vdash \ccase{e_1}{z{:}_{\overline{\Delta}^n}\sigma~\{\overline{\rho_i\to e_i}^n\}} : \varphi}
\\[1em]
    \judgment{\Gamma \vdash_{alt} \rho \to e : \sigma \Rightarrow \varphi}
\\[1em]
    \infer*[right=$(Alt)$]
    { K:\overline{\sigma\to_\pi}~T~\overline{p}\in\Gamma \and \Gamma, \overline{x{:}_\pi\sigma} \vdash e : \varphi}
    {\Gamma \vdash_{alt} K~\overline{x{:}_\pi\sigma} \to e : T~\overline{p} \Rightarrow \varphi}
\qquad
    \infer*[right=$(Alt_\_)$]
    { \Gamma \vdash e : \varphi }
    {\Gamma \vdash_{alt} \_ \to e : T~\overline{p} \Rightarrow \varphi}
\\[1em]
    \judgment{\Gamma \vdash_{mult} \pi}
\\[1em]
    \infer*[right=$(1)$]
    { }
    {\Gamma \vdash 1}
\qquad
    \infer*[right=$(\omega)$]
    { }
    {\Gamma \vdash \omega}
\qquad
    \infer*[right=$(\rho)$]
    { }
    {\Gamma, \rho \vdash \rho}
\\[1em]
\begin{array}{cc}
\judgment{\Gamma \vdash decl : \Gamma'} & \judgment{\Gamma \vdash pgm : \sigma}\\
\\[0.05em]
\infer*[right=$(Data)$]{ }{\Gamma \vdash (\datatype{T~\overline{p}}{\overline{K:\sigma}}) : (\overline{K:\sigma}) } &
\infer*[right=$(Pgm)$]{\overline{\Gamma \vdash decl:\Gamma_d} \and \Gamma = \Gamma_0,\overline{\Gamma_d}\\\\ \Gamma~\mathsf{is~consistent?} \and \Gamma \vdash e : \sigma}{\Gamma_0 \vdash \overline{decl}; e : \sigma}
\end{array}
\end{array}
\]
\end{framed}
\caption{Linear Core* Typing Rules}
\label{linear-core-typing-rules}
\end{figure}


\begin{figure}[h]
\begin{framed}
\small
\[
\begin{array}{l}
%
\textbf{Values} \\
\begin{array}{lcl}
    v & ::= & \Lambda p.~e \mid \lambda x.~e \mid K~\overline{v} \\
\end{array}\\\\
%
\textbf{Evaluation Contexts}\\
\begin{array}{llcl}
\infer{e \longrightarrow e'}{E[e] \longrightarrow E[e']} & E & ::= & \square \mid E~e \mid E~\pi \mid \ccase{E}{z{:}_{\overline{\Delta}}\sigma \{\overline{\rho \to e}\}} \\
\end{array}\\\\
%
\textbf{Expression Reductions}\\
\begin{array}{lcl}
(\Lambda p.~e)~\pi & \longrightarrow & e[\pi/p]\\
(\lambda x.~e)~e' & \longrightarrow & e[e'/x]\\
\llet{x{:}_\Delta\sigma = e}{e'} & \longrightarrow & e'[e/x]\\
\lletrec{\overline{x{:}_\Delta\sigma = e}}{e'} & \longrightarrow & e'\overline{[\lletrec{\overline{x{:}_\Delta\sigma = e}}{e}/x]}\\
\ccase{K~\overline{e}}{\dots K~\overline{x{:}_\pi\sigma} \to e'} &
\longrightarrow & e'[\overline{e}/\overline{x{:}_\pi\sigma}][K~\overline{e}/z]\\
\end{array}
\end{array}
\]
\end{framed}
%TODO: Addition and scaling usage environments
\caption{Linear Core* Operational Semantics \small(call-by-name)}
\label{linear-core-operational-semantics}
\end{figure}

\begin{figure}[h]
\begin{framed}
\small
\[
\begin{array}{c}
    \judgment{\Gamma \vdash e : \sigma \leadsto \Delta}
\\[1em]
    \infer*[right=($Var_\pi$)]
    { }
    {\Gamma, x{:}_\pi \sigma \vdash x : \sigma \leadsto \cdot,x{:}_\pi\sigma}
\qquad
    \infer*[right=($Var_\Delta$)]
    { }
    {\Gamma , x{:}_\Delta \sigma \vdash x : \sigma \leadsto \Delta}
\\[1em]
    % \Delta might have p, so on application be careful to substitute
    \infer*[right=($\Lambda I$)]
    {\Gamma, p \vdash e : \sigma \leadsto \Delta \and p \notin \Gamma}
    {\Gamma \vdash \Lambda p.~e : \forall p. \sigma \leadsto \Delta}
\qquad
    \infer*[right=($\Lambda E$)]
    {\Gamma \vdash e : \forall p.~\sigma \leadsto \Delta \and \Gamma \vdash_{mult} \pi}
    {\Gamma \vdash e~\pi : \sigma[\pi/p] \leadsto \Delta[\pi/p]}
\\[1em]
    \infer*[right=($\lambda I_1$)]
    {\Gamma, x{:}_1\sigma_1 \vdash e : \sigma_2 \leadsto \Delta,x{:}_1\sigma_1 \and x{:}_1\sigma_1\notin\Delta}
    {\Gamma \vdash \lambda x{:}_1\sigma_1.~e : \sigma_1 \to_\pi \sigma_2 \leadsto \Delta}
\\[1em]
    \infer*[right=($\lambda I_\omega$)]
    {\Gamma, x{:}_\omega\sigma_1 \vdash e : \sigma_2 \leadsto \Delta}
    {\Gamma \vdash \lambda x{:}_\omega\sigma_1.~e : \sigma_1 \to_\pi \sigma_2 \leadsto \Delta\!\upharpoonright_{\neq x}}
\\[1em]
    \infer*[right=($\lambda E$)]
    {\Gamma \vdash e_1 : \sigma_2 \to_\pi \sigma_1 \leadsto \Delta \and \Gamma \vdash e_2 : \sigma_2 \leadsto \Delta'}
    {\Gamma \vdash e_1~e_2 : \sigma_1 \leadsto \Delta + \Delta'}
\\[1em]
    \infer*[right=($Let$)]
    {\Gamma \vdash e_1 : \sigma_1 \leadsto \Delta \and \Gamma, x{:}_\Delta\sigma_1 \vdash e_2 : \sigma_2 \leadsto \Delta'}
    {\Gamma \vdash \llet{x{:}_\Delta\sigma_1 = e_1}{e_2} : \sigma_2 \leadsto \Delta'}
\\[1em]
    \infer*[right=($LetRec$)]
    { \overline{\Gamma, \overline{x{:}_1\sigma} \vdash e' : \sigma \leadsto \Delta_{naive}}\\
      \overline{\Delta} = \mathsf{computeRecUsages}(\overline{\Delta_{naive}}) \\
      \Gamma, \overline{x{:}_{\Delta}\sigma} \vdash e : \varphi \leadsto \Delta'
      }
    {\Gamma \vdash \lletrec{\overline{x{:}_{\Delta}\sigma = e'}}{e} : \varphi \leadsto \Delta'}
\\[1em]
    \infer*[right=($Case$)]
    { \Gamma \vdash e_1 : \sigma \leadsto \Delta \\
      \overline{\Gamma \vdash_{pat} \rho_i : \sigma \leadsto \Delta_i} \\\\
      \overline{\Gamma', z{:}_{\Delta_i}\sigma \vdash_{alt} \rho_i \to e_i : \sigma \Rightarrow \varphi \leadsto \Delta'} \and
      \overline{\Delta' \leq \Delta''}
      }
    {\Gamma, \Gamma' \vdash \ccase{e_1}{z{:}_{\overline{\Delta}^n}\sigma~\{\overline{\rho_i\to e_i}^n\}} : \varphi \leadsto \Delta + \Delta''}
\\[1em]
    \judgment{\Gamma \vdash_{pat} \rho : \sigma \leadsto \Delta}
\\[1em]
    \infer*[right=($pat$)]
    { }
    {\Gamma, K{:}\overline{\sigma\to_\pi}\varphi \vdash_{pat} K~\overline{x{:}_\pi\sigma}:\varphi \leadsto \cdot,\overline{x{:}_\pi\sigma}}
\\[1em]
    \judgment{\Gamma \vdash_{alt} \rho \to e : \sigma \Rightarrow \varphi \leadsto \Delta}
\\[1em]
    \infer*[right=$(Alt$)]
    { K:\overline{\sigma\to_\pi}~T~\overline{p}\in\Gamma \and \Gamma, \overline{x{:}_\pi\sigma} \vdash e : \varphi \leadsto \Delta}
    {\Gamma \vdash_{alt} K~\overline{x{:}_\pi\sigma} \to e : T~\overline{p} \Rightarrow \varphi \leadsto \Delta}\\
\qquad
    \infer*[right=$(Alt_\_)$]
    { \Gamma \vdash e : \varphi \leadsto \Delta }
    {\Gamma \vdash_{alt} \_ \to e : T~\overline{p} \Rightarrow \varphi \leadsto \Delta}
\end{array}
\]
\end{framed}
\caption{Linear Core* - Infer Usage Environments}
\label{linear-core-construct-usage-envs}
\end{figure}

\section{Type Soundness}

\clearpage
\begin{theorem}[Type preservation]
\emph{If $\Gamma \vdash e : \sigma$ and $e \to^* e'$ then $\Gamma \vdash e' : \sigma$}
\end{theorem}

\begin{proof}
By structural induction on the small-step reduction.

%   \begin{description}
%   \item[Case:] $\imp$-{\sc param}
%     \begin{tabbing}
%       $\Delta \vdash \alpha \imp \alpha$ \` this case\\
%       $\TERASE{\Delta}{\alpha} = t_I$, with $\bounds_\Delta(\alpha) =
%       t_I(\ov{\tau})$ \` by definition\\
%       $t_I \imp t_I$ \` by rule $\imp_I$
%     \end{tabbing}
%
%   \item[Case:] ...

\begin{description}

\item[Case:] $(\lambda x{:}_\pi\sigma.~e)~e' \longrightarrow e[e'/x]$
\begin{tabbing}
  (1) $\Gamma, \Gamma' \vdash (\lambda x{:}_\pi\sigma.~e)~e' : \varphi$ \` by assumption \\
  (2) $\Gamma \vdash (\lambda x{:}_\pi\sigma.~e) : \sigma\to_\pi\varphi$ \` by inversion on ($\lambda E$) \\
  (3) $\Gamma, x{:}_\pi\sigma \vdash e : \varphi$ \` by inversion on ($\lambda I$) \\
  (4) $\Gamma' \vdash e' : \sigma$ \` by inversion on ($\lambda E$) \\
  (5) $\Gamma, \Gamma' \vdash e[e'/x] : \varphi$ \` by subst. lemma (3,4) \\
\end{tabbing}

\item[Case:] $(\Lambda p.~e)~\pi \longrightarrow e[\pi/p]$
\begin{tabbing}
(1) $\Gamma \vdash (\Lambda p.~e)~\pi : \sigma[\pi/p]$ \` by assumption \\
(2) $\Gamma \vdash (\Lambda p.~e) : \forall p.~\sigma$ \` by inversion on ($\Lambda E$) \\
(3) \` $\Gamma \vdash_{mult} \pi$ \` by inversion on ($\Lambda E$) \\
(4) $\Gamma, p \vdash e : \sigma$ \` by inversion on ($\Lambda I$) \\
% TODO: How to use these inversions
(5) $p \notin \Gamma$ \` by inversion on ($\Lambda I$) \\
(6) $\Gamma \vdash e[\pi/p]:\sigma[\pi/p]$ \` by subst. lemma (3,4) \\
\end{tabbing}

\item[Case:] $\llet{x{:}_\Delta\sigma = e}{e'}\longrightarrow e'[e/x]$
\begin{tabbing}
(1) $\Gamma \vdash \llet{x{:}_\Delta\sigma = e}{e'} : \varphi$ \` by assumption \\
(2) $\Gamma, x{:}_\Delta\sigma \vdash e' : \varphi$ \` by inversion on (let) \\
(3) $\Delta \vdash e : \sigma$ \` by inversion on (let) \\
(4) $\Delta \subseteq \Gamma$ \` by inversion on (let) \\
(5) $\Gamma \vdash e'[e/x] : \varphi$ \` by subst. lemma (2,3,4?) \\
\end{tabbing}

\item[Case:] $\llet{\overline{x{:}_\Delta\sigma = e}}{e'} \longrightarrow e'\overline{[\lletrec{\overline{x{:}_\Delta\sigma = e}}{e}/x]}$
\begin{tabbing}
(1) $\Gamma \vdash \llet{\overline{x{:}_\Delta\sigma = e}}{e'} : \varphi$ \` by assumption \\
(2) $\Gamma, \overline{x{:}_\Delta\sigma} \vdash e : \varphi$ \` by inversion on (letrec) \\
(3) $\overline{\Delta, \overline{x{:}_\Delta\sigma \vdash e' : \sigma}}$ \` by inversion on (letrec) \\
(4) $\overline{\Delta\subseteq\Gamma}$ \` by inversion on (letrec) \\
(5) $\Gamma \vdash e'\overline{[\lletrec{\overline{x{:}_\Delta\sigma = e}}{e}/x]}$ \` by subst. lemma (2,3,4?) \\
\end{tabbing}

\item[Case:] $\ccase{K~\overline{e}}{z{:}_{\overline{\Delta}}\sigma}~\{\dots,K~\overline{x{:}_\pi\sigma}\}\ \longrightarrow e'[\overline{e}/\overline{x}][K~\overline{e}/z]$
\begin{tabbing}
(1) $\Gamma,\Gamma' \vdash \ccase{K~\overline{e}}{z{:}_{\overline{\Delta}}\sigma~\{\dots,K~\overline{x{:}_\pi\sigma}\to e'\}} : \varphi$ \` by assumption \\
(2) $\Gamma \vdash K~\overline{e} : \sigma$ \` by inversion on (case) \\
(3) $\Gamma', z{:}_\Delta\sigma \vdash_{alt} K~\overline{x{:}_\pi\sigma} \to e' : \sigma \Longrightarrow \varphi$ \` by inversion on (case) \\
% TODO: Como é que uso estes casos
(4) $K : \overline{\sigma \to_\pi} T~\overline{p} \in \Gamma'$ \` by inversion on (alt) \\
(5) $\Gamma',z{:}_\Delta\sigma,\overline{x{:}_\pi\sigma} \vdash e' : \varphi$ \` by inversion on (alt) \\
% TODO: Delta_i?
(6) $\Gamma, z{:}_{\Delta_i}\sigma, \Gamma' \vdash e'[\overline{e}/\overline{x}] : \varphi$ \` by subst. lemma (2,5) \\
% TODO: HOW? Missing something (inversion on case). Hard!
(7) $\Gamma, \Gamma' \vdash e'[\overline{e}/\overline{x}][???/z]$ \` by subst. lemma (6,2) \\
\end{tabbing}

\item[Case:] $e_1~e_2 \longrightarrow e_1'~e_2$
\begin{tabbing}
(1) $e_1 \longrightarrow e_1'$ \` by inversion on $\beta$-reduction \\
(2) $\Gamma,\Gamma' \vdash e_1~e_2 : \varphi$ \` by assumption \\
(3) $\Gamma \vdash e_1 : \sigma \to_\pi \varphi$ \` by inversion on ($\lambda E$) \\
(4) $\Gamma' \vdash e_2 : \sigma$ \` by inversion on ($\lambda E$) \\
(5) $\Gamma \vdash e_1' : \sigma \to_\pi \varphi$ \` by induction hypothesis in (3,1) \\
(6) $\Gamma, \Gamma' \vdash e_1'~e_2 : \varphi$ \` by ($\lambda E$) (4,3) \\
\end{tabbing}

\item[Case:] $e~\pi \longrightarrow e'~\pi$
\begin{tabbing}
(1) $e \longrightarrow e'$ \` by inversion on mult. $\beta$-reduction \\
(2) $\Gamma \vdash e~\pi : \sigma[\pi/p]$ \` by assumption \\
(3) $\Gamma \vdash e : \forall p.~\sigma$ \` by inversion on ($\Lambda E$) \\
(4) $\Gamma \vdash_{mult} \pi$ \` by inversion on ($\Lambda E$) \\
(5) $\Gamma \vdash e' : \forall p.~\sigma$ \` by induction hypothesis (3,1) \\
(6) $\Gamma \vdash e'~\pi : \sigma[\pi/p]$ \` by ($\Lambda E$) (5,4) \\
\end{tabbing}

\item[Case:] $\ccase{e}{z{:}_{\overline{\Delta}}\sigma~\{\rho_i\to e'_i\}} \longrightarrow \ccase{e'}{z{:}_{\overline{\Delta}}\sigma~\{\rho_i\to e'_i\}}$
\begin{tabbing}
(1) $e \longrightarrow e'$ \` by inversion on case reduction \\
(2) $\Gamma, \Gamma' \vdash \ccase{e}{z{:}_{\overline{\Delta}}\sigma~\{\rho_i\to e'_i\}} : \varphi$ \` by assumption \\
(3) $\Gamma \vdash e : \sigma$ \` by inversion on case \\
% TODO: HOW i?
(4) $\overline{\Gamma', z{:}_{\Delta_i}\sigma \vdash_{alt} \rho_i \to e'_i : \varphi}$ \` by inversion on case \\
(5) $\Gamma \vdash e' : \sigma$ \` by induction hypothesis (3,1) \\
(6) $\Gamma, \Gamma' \vdash \ccase{e'}{z{:}_{\overline{\Delta}}\sigma~\{\rho_i\to e'_i\}} : \varphi$ \` by case (4,3) \\
\end{tabbing}

\end{description}

\end{proof}

\clearpage
\begin{theorem}[Progress]
\emph{Evaluation of a well-typed term does not block. If $\cdot \vdash e : \sigma$ then $e$ is a value or there exists $e'$ such that $e \to e'$.}
\end{theorem}

\begin{proof}
By structural induction on the (only) typing derivation

\begin{description}

\item[Case:] $\Lambda I$
\begin{tabbing}
(1) $\cdot \vdash (\Lambda p.~e) : \forall p.~\sigma$ \` by assumption \\
(2) $(\Lambda p.~e)~\textrm{is a value}$ \` by definition \\
\end{tabbing}

\item[Case:] $\Lambda E$
\begin{tabbing}
(1) $\cdot \vdash e_1~\pi : \sigma[\pi/p]$ \` by assumption \\
(2) $\cdot \vdash e_1 : \forall p.~\sigma$ \` by inversion on ($\Lambda E$) \\
(3) $\cdot \vdash_{mult} \pi$ \` by inversion on ($\Lambda E$) \\
(4) $e_1~\textrm{is a value or}~\exists e_1'. e_1 \longrightarrow e_1'$ \` by the induction hypothesis (2) \\
\textrm{Subcase $e_1$ is a value:}\\
(5) $e_1 = \Lambda p.~e_2$ \` by the canonical forms lemma (2) \\
(6) $(\Lambda p.~e_2)~\pi \longrightarrow e_2[\pi/p]$ \` by $\beta$-reduction on multiplicity (5,3) \\
\textrm{Subcase $e_1 \longrightarrow e_1'$:}\\
% TODO: Have I've concluded two different things in the proof because
% the reductions don't match (on one we have explicit substitution)?
(5) $e_1~\pi \longrightarrow e_1'~\pi$ \` by context reduction on mult. application \\
\end{tabbing}

\item[Case:] $\lambda I$
\begin{tabbing}
(1) $\cdot \vdash (\lambda x{:}_\pi\sigma.~e) : \sigma\to_\pi\varphi$ \` by assumption \\
(2) $(\lambda x{:}_\pi\sigma.~e)~\textrm{is a value}$ \` by definition \\
\end{tabbing}

\item[Case:] $\lambda E$
\begin{tabbing}
(1) $\cdot \vdash e_1~e_2 : \varphi$ \` by assumption \\
(2) $\cdot \vdash e_1 : \sigma \to_\pi \varphi$ \` by inversion on ($\lambda E$) \\
(3) $\cdot \vdash e_2 : \sigma$ \` by inversion on ($\lambda E$) \\
(4) $e_1~\textrm{is a value or}~\exists e_1'. e_1\longrightarrow e_1'$ \` by the induction hypothesis (2) \\
\textrm{Subcase $e_1$ is a value:}\\
(5) $e_1 = \lambda x{:}_\pi\sigma.~e$ \` by the canonical forms lemma \\
(6) $e_1~e_2 \longrightarrow e[e_2/x]$ \` by term $\beta$-reduction (5,3) \\
\textrm{Subcase $e_1\longrightarrow e_1'$:}\\
(5) $e_1~e_2\longrightarrow e_1'~e_2$ \` by context reduction on term application \\
\end{tabbing}

\item[Case:] $Let$
\begin{tabbing}
(1) $\cdot \vdash \llet{x{:}_\Delta\sigma = e}{e'} : \varphi$ \` by assumption \\
(2) $\llet{x{:}_\Delta\sigma = e}{e'}\longrightarrow e'[e/x]$ \` by definition of reduction. Wait, what? \\
\end{tabbing}

\item[Case:] $LetRec$
\begin{tabbing}
(1) $\cdot \vdash \lletrec{\overline{x{:}_\Delta\sigma = e}}{e'} : \varphi$ \` by assumption \\
(2) $\lletrec{\overline{x{:}_\Delta\sigma = e}}{e'} \longrightarrow e'\overline{[\lletrec{\overline{x{:}_\Delta\sigma = e}}{e}/x]}$ \` by definition of reduction. \\
\end{tabbing}

\item[Case:] $Case$
\begin{tabbing}
(1) $\cdot \vdash \ccase{e}{z{:}_{\overline{\Delta}}\sigma~\{\overline{\rho_i \to e_i}\}} : \varphi$ \` by assumption \\
(2) $\cdot \vdash e_1 : T~\overline{p}$ \` by inversion of (case) \\
% ROMES:TODO What to do about z
(3) $\overline{\cdot, z{:}_{\overline{\Delta}}\sigma \vdash_{alt} \rho_i\to e_i : \sigma \Longrightarrow \varphi}$ \` by inversion of (case) \\
(4) $e_1~\textrm{is a value or}~\exists e_1'. e_1 \longrightarrow e_1'$ \` by induction hypothesis (2) \\
\textrm{Subcase $e_1$ is a value:}\\
(5) $e_1 = K~\overline{e}$ \` by canonical forms lemma \\
(6) $\ccase{e_1}{z{:}_{\overline{\Delta}}\sigma~\{\overline{\rho_i \to e_i}\}} \longrightarrow e'[\overline{e}/\overline{x{:}_\pi\sigma}][K~\overline{e}/z]$ \` by case reduction (5) \\
\textrm{Subcase $e_1 \to e_1'$:}\\
(5) $\ccase{e_1}{z{:}_{\overline{\Delta}}\sigma~\{\overline{\rho_i \to e_1}\}} \longrightarrow \ccase{e_1'}{z{:}_{\overline{\Delta}}\sigma~\{\rho_i \to e_i\}}$ \` by context reduction \\
\end{tabbing}

\end{description}

\end{proof}


\clearpage
\begin{lemma}[Substitution]
\emph{If $\Gamma, x{:}_1\sigma \vdash e : \varphi$ and $\cdot \vdash e' : \sigma$ then $\Gamma \vdash e[e'/x] : \varphi$}
\end{lemma}

\begin{proof}
By structural induction on the first derivation.

\begin{description}

\item[Case:] $Var_1$
\begin{tabbing}
  (1) $\cdot,x{:}_1\sigma \vdash x : \sigma$ \` by assumption\\
  (2) $\cdot \vdash e' : \sigma$ \` by assumption\\
  (3) $x[e'/x] = e'$ \` by def. of substitution\\
  (4) $\cdot \vdash e' : \sigma$ \` by (1,2,3)\\
\end{tabbing}

\item[Case:] $Weaken_\omega$
\begin{tabbing}
  (1) $\Gamma, x{:}_1\omega, y{:}_\omega\sigma' \vdash e : \varphi$ \` by assumption\\
  (2) $\cdot \vdash e' : \sigma$ \` by assumption\\
  (3) $\Gamma, x{:}_1\sigma \vdash e : \varphi$ \` by inversion on $Weaken_\omega$\\
  (4) $\Gamma \vdash e[e'/x] : \varphi$ \` by induction hypothesis by (2,3)\\
  (5) $\Gamma, y{:}_\omega\sigma' \vdash e[e'/x] : \varphi$ \` by $Weaken_\omega$ (4)\\
\end{tabbing}

\item[Case:] $Weaken_\Delta$\\
Just like $Weaken_\omega$ with \texttt{s/omega/Delta}

\item[Case:] $Contract_\omega$
\begin{tabbing}
  (1) $\Gamma, x{:}_1\sigma, y{:}_\omega\sigma' \vdash e : \varphi$ \` by assumption\\
  (2) $\cdot \vdash e' : \sigma$ \` by assumption\\
  (3) $\Gamma, x{:}_1\sigma, y{:}_\omega\sigma', y{:}_\omega\sigma' \vdash e : \varphi$ \` by inversion on $Contract_\omega$\\
  (4) $\Gamma, y{:}_\omega\sigma', y{:}_\omega\sigma' \vdash e[e'/x] : \varphi$ \` by induction hypothesis by (2,3)\\
  (5) $\Gamma, y{:}_\omega\sigma' \vdash e[e'/x] : \varphi$ \` by $Contract_\omega$ (4)\\
\end{tabbing}

\item[Case:] $Contract_\Delta$\\
Just like $Contract_\omega$ with \texttt{s/omega/Delta}

\item[Case:] $Var_\omega$\\
  Impossible, $x{:}_1\sigma$ can't be in this rule's context

\item[Case:] $Var_\Delta$
\begin{tabbing}
  (1) $\Gamma, x{:}_1\sigma, y{:}_\Delta\sigma' \vdash e : \varphi$ \` by assumption\\
  (2) $\cdot \vdash e' : \sigma$ \` by assumption\\
  (3) $\Delta\!\upharpoonright_1 = \Gamma$ \` by inversion on $Var_\Delta$\\
  (4) Stuck
\end{tabbing}

\item[Case:] $\Lambda I$
\begin{tabbing}
  (1) $\Gamma, x{:}_1\sigma \vdash \Lambda p.~e : \forall p.~\varphi$ \` by assumption\\
  (2) $\cdot \vdash e' : \sigma$ \` by assumption\\
  (3) $\Gamma, x{:}_1\sigma, p \vdash e : \varphi$ \` by inversion on $\Lambda I$\\
  (4) $p \notin \Gamma$ \` by inversion on $\Lambda I$\\
  (5) $\Gamma, p \vdash e[e'/x] : \varphi$ \` by induction hypothesis by (2,3)\\
  (6) $\Gamma \vdash \Lambda p.~e[e'/x] : \forall p.~\varphi$ \` by $\Lambda I$ (4,5)\\
  (7) $(\Lambda p.~e)[e'/x] = (\Lambda p.~e[e'/x])$ \` by def. of substitution\\
\end{tabbing}

\item[Case:] $\Lambda E$
\begin{tabbing}
  (1) $\Gamma, x{:}_1\sigma \vdash e~\pi: \varphi[\pi/p]$ \` by assumption\\
  (2) $\cdot \vdash e' : \sigma$ \` by assumption\\
  (3) $\Gamma, x{:}_1\sigma \vdash e : \forall p.~\varphi$ \` by inversion on $\Lambda E$\\
  (4) $\Gamma, x{:}_1\sigma \vdash_{mult} \pi$ \` by inversion on $\Lambda E$\\
  (5) $\Gamma \vdash e[e'/x] \forall p.~\varphi$ \` by induction hypothesis by (2,3)\\
  (6) $\Gamma \vdash e[e'/x]~\pi : \varphi[\pi/p]$ \` by $\Lambda E$ (4,5)\\
  (7) $(e~\pi)[e'/x] = e[e'/x] \pi$ \` by def. of substitution\\
\end{tabbing}

\item[Case:] $\lambda I$
\begin{tabbing}
  (1) $\Gamma, x{:}_1\sigma \vdash \lambda y{:}_\pi\sigma'.~e : \sigma' \to_\pi \varphi$ \` by assumption\\
  (2) $\cdot \vdash e' : \sigma$ \` by assumption\\
  (3) $\Gamma, x{:}_1\sigma, y{:}_\pi\sigma' \vdash e : \varphi$ \` by inversion on $\lambda I$\\
  (4) $\Gamma, y{:}_\pi\sigma' \vdash e[e'/x] : \varphi$ \` by induction hypothesis by (2,3)\\
  (5) $\Gamma \vdash \lambda y{:}_\pi\sigma'.~e[e'/x] : \sigma' \to_\pi \varphi$ \` by $lLambda I$ (4)\\
  (6) $(\lambda y{:}_\pi\sigma'.~e)[e'/x] = (\lambda y{:}_\pi\sigma'.~e[e'/x])$ \` by def. of substitution\\
\end{tabbing}

\item[Case:] $\lambda E_1$ (linear variable occurs in function)
\begin{tabbing}
  (1) $\Gamma, x{:}_1\sigma, \Gamma' \vdash e~e'' : \varphi$ \` by assumption\\
  (2) $\cdot \vdash e' : \sigma$ \` by assumption\\
  (3) $\Gamma, x{:}_1\sigma \vdash e : \sigma' \to_\pi \varphi$ \` by inversion on $\lambda E$\\
  (4) $\Gamma' \vdash e'' : \sigma'$ \` by inversion on $\lambda E$\\
  (5) $\Gamma \vdash e[e'/x] : \sigma' \to_\pi \varphi$ \` by induction hypothesis by (2,3)\\
  (6) $\Gamma, \Gamma' \vdash e[e'/x]~e'' : \varphi$ \` by $\lambda E$\\
  (7) $(e~e'')[e'/x] = (e[e'/x]~e'')$ \` by in def. of linear substitution 1\\
\end{tabbing}

\item[Case:] $\lambda E_2$ (linear variable occurs in argument)
\begin{tabbing}
  (1) $\Gamma, \Gamma', x{:}_1\sigma \vdash e~e'' : \varphi$ \` by assumption\\
  (2) $\cdot \vdash e' : \sigma$ \` by assumption\\
  (3) $\Gamma \vdash e : \sigma' \to_\pi \varphi$ \` by inversion on $\lambda E$\\
  (4) $\Gamma', x{:}_1\sigma \vdash e'' : \sigma'$ \` by inversion on $\lambda E$\\
  (5) $\Gamma' \vdash e''[e'/x] : \sigma'$ \` by induction hypothesis by (2,4)\\
  (6) $\Gamma, \Gamma' \vdash e~e''[e'/x] : \varphi$ \` by $\lambda E$\\
  (7) $(e~e'')[e'/x] = (e~e''[e'/x])$ \` by def. of linear substitution 2\\
\end{tabbing}

\end{description}

\end{proof}

