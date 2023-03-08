%include polycode.fmt

\renewcommand{\llet}[2]{\mathbf{let}~#1~\mathbf{in}~#2}
\renewcommand{\lletrec}[2]{\mathbf{let~rec}~#1~\mathbf{in}~#2}
\renewcommand{\ccase}[2]{\mathbf{case}~#1~\mathbf{of}~#2}

\chapter{Linear Core*}

\begin{figure}[h]
\begin{framed}
\[
\begin{array}{l}
%
\textbf{Types} \\
\begin{array}{lcll}
    \varphi,\sigma & ::= & D~p_1 \dots p_2 & \textrm{Datatype} \\
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
                    & \mid & \ccase{e_1}{z{:}_{\overline{\Delta}}~\{\overline{pat\to e_2}\}}   & \textrm{Case} \\
                    &      &                                    & \\
%    p               & ::= & K~\overline{b{:}\kappa}~\overline{x{:}\sigma} & \textrm{Pattern} \\
    pat             & ::= & K~\overline{b}~\overline{x{:}\sigma} & \textrm{Pattern with existential multiplicities} \\
% Currently we don't care about the existential multiplicity variables, but later on we might
\end{array}\\\\
%
\textbf{Environments}\\
\begin{array}{lcll}
  \Gamma & ::= & \epsilon & \textrm{Empty environment} \\
         & \mid & \Gamma,u{:}_\pi\sigma & \textrm{Lambda bound variable} \\
         & \mid & \Gamma,u{:}_\Delta\sigma & \textrm{Let(rec) bound variable}\\
         & \mid & \Gamma,u{:}_{\overline{\Delta}}\sigma & \textrm{Case bound variables}
\end{array}\\\\
%
\textbf{Multiplicities}\\
\begin{array}{lcll}
  \pi, \mu & ::= & 1 \mid \omega \mid p \mid \pi + \mu \mid \pi \cdot \mu\\
% We don't use + and cdot yet, but we will
\end{array}\\\\
%
\textbf{Usage Environments}\\
\begin{array}{lcll}
  \Delta & ::= & \epsilon \mid \Delta, x{:}_\pi\sigma \\
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
    \infer*[right=($Weaken_\omega$)]
    {\Gamma \vdash u : \sigma}
    {\Gamma , u{:}_\omega \sigma \vdash u : \sigma}
\qquad
    \infer*[right=($Weaken_\Delta$)]
    {\Gamma \vdash u : \sigma}
    {\Gamma , u{:}_\Delta \sigma \vdash u : \sigma}
\\[1em]
    \infer*[right=($Contract_\omega$)]
    {\Gamma , u{:}_\omega \sigma, u{:}_\omega \sigma \vdash u : \sigma}
    {\Gamma , u{:}_\omega \sigma \vdash u : \sigma}
\qquad
    \infer*[right=($Contract_\Delta$)]
    {\Gamma , u{:}_\Delta \sigma, u{:}_\Delta \sigma \vdash u : \sigma}
    {\Gamma , u{:}_\Delta \sigma \vdash u : \sigma}
\\[1em]
    % estranho para multiplicidades que não 1 e \omega, pode estar errado
    \infer*[right=($Var_\pi$)]
    { \{u{:}_\pi\}_1^\pi = \Gamma }
    {\Gamma , u{:}_\pi \sigma \vdash u : \sigma}
\qquad
    \infer*[right=($Var_\Delta$)]
    { \Delta = \Gamma }
    {\Gamma , u{:}_\Delta \sigma \vdash u : \sigma}
\\[1em]
% ROMES:TODO: Isto significa que precisamos de uma variável de multiplicidade no environment?
% Preciso de p \noin \Gamma?
    \infer*[right=($\Lambda I$)]
    {\Gamma, (p?) \vdash e : \sigma}
    {\Gamma \vdash \Lambda p.~e : \forall p. \sigma}
\qquad
% ROMES:TODO: Parece-me que precisamos de pensar melhor nas multiplicity abstractions, e de alguma forma tê-las no environment pode fazer sentido
% Não acho que percebo totalmente o suficiente estas regras
    \infer*[right=($\Lambda E$)]
    {\Gamma \vdash e : \forall p.~\sigma}
    {\Gamma \vdash e~\pi : \sigma[\pi/p]}
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
    {\Gamma, x{:}_\Delta\sigma_1 \vdash e : \sigma_2 \and \Delta \vdash u : \sigma_1 \and \Delta \subset \Gamma}
    {\Gamma \vdash \llet{x{:}_\Delta\sigma_1 = u}{e} : \sigma_2}
    % em alternativa a isto que está errado (separar o \Gamma em \Gamma, \Delta)
    % \infer*[right=($Let_{Wrong}$)]
    % {\Gamma, x{:}_\Delta\sigma_1 \vdash e : \sigma_2 \and \Delta \vdash u : \sigma_1}
    % {\Gamma,\Delta \vdash \llet{x{:}_\Delta\sigma_1 = u}{e} : \sigma_2}
\\[1em]
    % \infer*[right=($LetRec$)]
    % {\Gamma, \overline{x_n{:}_{\Delta_n}\sigma_n } \vdash e : \varphi \and \overline{\Delta_n \vdash u_n : \sigma_n}}
    % {\Gamma \vdash \lletrec{\overline{x_n{:}_{\Delta_n}\sigma_n = u_n}}{e} : \varphi}
    \infer*[right=($LetRec$)]
    {\Gamma, \overline{x_n{:}_{\Delta_n}\sigma_n } \vdash e : \varphi \and \overline{\Delta_n \vdash u_n : \sigma_n} \and \forall_n . \Delta_n \subset \Gamma}
    {\Gamma \vdash \lletrec{\overline{x_n{:}_{\Delta_n}\sigma_n = u_n}}{e} : \varphi}
\\[1em]
    \infer*[right=($Case$)]
    { }
    {\Gamma \vdash \ccase{e_1}{z{:}_{\overline{\Delta}}~\{\overline{pat\to e_2}\}} : \varphi}
\end{array}
\]
\end{framed}
\caption{Linear Core* Typing Rules}
\label{linear-core-syntax}
\end{figure}

