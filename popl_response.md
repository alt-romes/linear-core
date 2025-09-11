# POPL '26 Paper 572 -- Author Response

We would like to thank the reviewers for their reviews.

Following the Chair's instructions, our reply is in three parts:

1. Overview -- summary of key points
2. Change List -- our proposed revisions
3. Detailed Response -- answers to each reviewer's questions

---

## 1. Overview

### (a) Design tradeoffs viz. adapting transformation passes and simplifying Linear Core / comparing against a baseline syntactic linear type system for Core.

> **Reviewer A**: *Step back and explain the design tradeoffs. Could you have done some more work to adapt the transformation passes and simplify the design of Linear Core?*

> **Reviewer C**: *Do you have any sense of what the improvement would be if compared against a baseline syntactic linear type system for Core, i.e. Bernardy, et al. but for Core?*

The Linear Haskell implementation in GHC originally included a direct linearity checker for Core,
to be run as part of the internal validation passes of the compiler. The developers realized
that optimisation passes very frequently produced code that did not pass the linearity
check. Attempts to make the code pass the linearity checks were extremely challenging due
to a plethora of corner cases and, since transformations had to often be restricted, significant runtime performance degradation. After some time, all the linearity-related special cases in transformations ended up being removed. 

A brief report on this can be found in the GHC source code and issues (e.g. https://gitlab.haskell.org/ghc/ghc/-/issues/22123), noting that "linting linearity" is the internal terminology for linearity checking:
> Note [Linting Linearity]:
> [...]
> Historical note: In the original linear-types implementation, we had tried to
> make every optimisation pass produce code that passes -dlinear-core-lint. It
> had proved very difficult. We kept finding corner case after corner
> case. Furthermore, to attempt to achieve that goal we ended up restricting
> transformations when -dlinear-core-lint couldn't typecheck the result.
> 
> In the future, we may be able to lint the linearity of the output of
> Core-to-Core passes (#19165). But this shouldn't be done at the expense of
> producing efficient code. Therefore we lay the following principle.
> 
> PRINCIPLE: The type system bends to the optimisation, not the other way around.

Our work adheres to these design principles, at the cost of a more complex Linear Core.
We will reference this principle in our revision to make the tradeoffs clear.

### (b) Key ideas of Linear Core 

> **Reviewer B**: *What are the key ideas that make your core language work? Are there new ideas involved, or is it a combination of existing ideas?*

The key ideas that make Linear Core work are:
1. Usage environments (Section 3.3)
2. Distinct treatment of case scrutinees in WHNF (Section 3.6.1)
3. Proof irrelevant and tagged resources (Sections 3.6.2 and 3.6.3)

(1) Encodes the idea that lazy bindings do not consume resources upon definition, but rather when the bound variables themselves are consumed. Consuming a variable with usage environment Delta equates to consuming the variables in Delta.
(2) Case expressions in WHNF may capture ambient linear resources, but these resources can be safely used in branches since the case will not further evaluate its scrutinee. On the other hand, a case on a non-WHNF expression must be treated more conservatively. 
(3) Irrelevant resources make existing bindings unusable while forcing the use of others. Namely, linear resources occurring in non-WHNF case scrutinees can no longer be used in the alternative, while the pattern variables or the case binder must necessarily be used. Tagged resources follow the observation that some variables must be used jointly or not at all.

The usage environment idea was present in the unpublished Linear MiniCore draft (J. Bernardy et al. 2020), but was sketched for non-recursive lets only (as reported in Section 6). Points (2) and (3) above are specific to our work, although irrelevant resources have some similarities with other work (e.g. values with 0 multiplicity (Brady 2021), or proof irrelevance in type theory), as do tagged resources (i.e. fractional permissions in separation logic (Boyland 2003)). Our discussion of these similarities is mentioned throughout the paper. We will revise the related work section accordingly to refer to these papers in a more cohesive form.

### (c) Semantic notion of linearity

> **Reviewer A**: *you are not defining a semantic notion of linearity. Rather, you're designing a typing discipline which fits the lazy semantics of linearity.*

We concur that we are not defining a (new) notion of semantic linearity. Indeed, our definition is essentially that of Linear Haskell and our work establishes a new syntactic definition of linearity that is more precise wrt the semantic notion. We thank the reviewer for this perspective and we plan to rewrite our positioning accordingly.

### (d) Linearity in the presence of exceptions

> **Reviewer A**: *One of the main criticism of Linear Haskell is that it does not preserve linearity in the presence of exceptions.*

The reviewer is correct in that Linear Haskell has no special treatment of exceptions. This is also the case in GHC Core, where exceptions have no special status in Core code and so there is no natural way
of dealing of the interaction between exceptions and linearity in Core itself without a major overhaul of the exception mechanisms of the language.
Our work simply preserves the exceptional behaviour of the source and we will clarify this in our revision.
We note that `linear-base` has library-level abstractions that guarantee all accquired resources are released upon an exception. We refer to https://www.tweag.io/blog/2020-02-19-linear-type-exception/ for further details.


## 2. Change List

We will address all of the points raised by the reviewers:

- Revise introductory examples to more adequately flesh out the relevant points (**Reviewer A**).
- Revise the paper title and abstract, emphasizing the more general contributions (**Reviewer B**).
  We plan to change the title along the lines of "Semantic Linearity in a Lazy Optimising Compiler", 
  removing the subtitle.
- Revise introduction to more clearly flesh out key ideas, contributions, target audience and relationship
  with semantic linearity (**Reviewers A, B, C**).
- Address all minor corrections and presentation issues raised by the reviewers, expanding explanations
as requested (**Reviewers A, B and C**).

The above work is readily feasible before the 2nd round revision deadline (23rd Oct).

## 3. Detailed Response


### Reviewer A

> Step back and explain the design tradeoffs. Could you have done some more work to adapt the transformation passes and simplify the design of Linear Core?

See **Overview (a)**.

> The statement of contributions should be rewritten, and the abstract adapted. See below, but in short, you are not defining a semantic notion of linearity. 

We will adjust both the contributions and the abstract accordingly. See **Overview (c)** and **Change list**.

> Introductory examples should be chosen better.

We will revise the introductory examples to more meaningfully use variables in their control-flow branches, as stated
in the **Change list**.

> Please don't omit relative pronouns.

These fall under the minor corrections and presentation issues mentioned in the **Change list**.

> “conservatively treating all multiplicity polymorphic functions as linear,”: Is this really "conservative"? 

Our text is imprecise. Our minimal treatment of multiplicity polymorphism simply treats variables that are multiplicity polymorphic parametrically. In fact, we omitted a variable rule for multiplicity polymorphic variables:

``` 
rho in Gamma
---------------------------
Gamma ; x:_rho T |- x: T
```

We will implement this correction in our revision.


> “Γ, 𝑥:Δ 𝜎; Δ ⊢ 𝑥 : 𝜎”: I'm guessing that the two occurrences of Δ refer to different things. Clarify or repair.

Our goal with this notation is to assert that the usage environment associated with variable `x` is Δ, which consists exactly of all ambient linear variables which are tracked by context Δ. The two Δ are indeed the same. We understand that dubbing them Δ-bound variables adds confusion since it makes it seem as if Δ is terminal in the grammar. We will rephrase as usage-bound variables and clarify this in our revision.

> Fig 4. “CaseWHNF”: this rule is unparseable for me. 

The typesetting of the rule is unfortunate. The premises in the topline state, in order, that e is in WHNF; e is of type $\sigma$ with ocurring linear variables $\overline{\Delta_i}$ and that e matches with branch $\rho_j$. The two bottom premises appeal to the pattern judgment for WHNF scrutinees for pattern $\rho_j$ (where the $\overline{\Delta_i}$ may be consumed through the case-binder or outright) and the NWHNF pattern judgment for the remaining branches (where the $\overline{\Delta_i}$ may only be consumed via the case-binder). We will expand the explanation at the end of Section 3.6.2 and we will fix the type-setting issue (**Change list**).

> Fig 4. The Last judgement has 6 or 7 argument and I don't know how many fixed parts.

We will fix the type-setting issue (**Change list**).

> Inference of usage environments for recursive lets.
> Do you simply mean that if one writes the annotations then it suffices to check them?

We acknowledge the chosen phrasing was a bit barroque. Yes the annotations needs only be checked. See the response regarding the use of Delta above, clarifying that the use of Delta is not a terminal symbol but rather an actual context of variables.

> Perhaps there should be a discussion of whether doing "case" on a WHNF expression is useful at all. I guess this is motivated by practical considerations, please spell them out at this point.

Case-ing on a WHNF arises frequently due to the chaining of optimizing transformations. We will further emphasize this at this point in the paper (we briefly mention this in L319 and L751).

> - “we must branch on weak head normal formed-ness to accurately type expression”: -> accurate typing of case expressions depends on whether the scrutinee is in WHNF.

See **Change list**.

> Clarify Γ[Δ/x], and Γ[𝑥/[Δ]]
> “𝑥: [Δ]”: At this point I realize that I don't understand the difference between Δ and [Δ]. Did I miss something? If so a back-reference to the explanation would help.

We use Γ[Δ/x] to denote a substitution of x by Δ in occurrences in the usage
environments of variables in Γ. Example: (y:_{a,b})[{c,d}/a] ==> y:_{c,d,b}.

Accordingly, Γ[𝑥/[Δ]] substitutes occurrences of the whole environment of
irrelevant variables ([Δ]) for x in the usage environments of variables in Γ.
Example: (y_{[a],[b],c}[[{a,b}]/x]) ==> y_{x,c}.

The introduction of the bracket notation is given in Section 3.6.2, L721. We will revise accordingly to make this more upfront.

> “Proof irrelevant”: I was already confused by this term earlier (what are proofs here? does this mean simply unused?) But the repeated use of "proof" in this paragraph makes me very confused.

Proof irrelevant variables cannot be used. The terminology is borrowed from type theory (e.g. (Pfenning '01)), but we understand this might be confusing and does not line up exactly with the type theoretic constructions. We will revise this terminology to simply "irrelevant" and clarify its meaning. 

Frank Pfenning. Intensionality, Extensionality, and Proof Irrelevance in Modal Type Theory. LICS 2001.

### Reviewer B

> What are the key ideas that make your core language work?

See **Overview (b)**.

> 1, The title needs further work. The present version seems to be trying to say that the approach is both general (the main title) and specific (the subtitle), but doesn't read well. I'd suggest going for a simpler and more direct title that doesn't try to cover two bases at the same time.
> 6, The first paragraph of the abstract is a bit verbose and could be compressed quite a bit. After doing so it probably makes sense to make the abstract a single paragraph.

This issue was also raised by Reviewer A. We will address this in our revision (see **Change list**).

> 107, Explain who the paper is targeted at, e.g. what kind of knowledge and experience is required. It is also important to clarify here that while Haskell is the focus of the paper, the ideas can potentially be applied to any language with non-strict features, even if the language itself is strict.

We will clarify the generality of our approach in terms of non-strict language features (see **Change list**).

> 107, The paper contains an appendix with 28 pages of material, whereas the call for papers states that each paper should have no more than 25 pages of text, excluding bibliography. Any additional material should be included as supplementary material separate from the main paper, rather than as an appendix.

We will move this content into supplementary materials. 

> 115, There are a lot of parenthetical remarks in the paper, which are quite distracting. It would be beneficial to try and minimise the use of this feature.

See **Change list**.

> 137, Why are two different colours (yellow and orange) used for programs that are semantically linear but not linear in Core?

This was unclear in our prose. Yellow means accepted by our work, orange means not accepted by our work. We will
clarify.

> 330, Explain the rationale for the choice of superscript and subscript on the linear calculus dubbed LinearCore.

The formalism that forms the basis for Linear Haskell is dubbed $\lambda^Q_\rightarrow$, due to having multiplicities (p,q) and linearity information in the arrow type. We identified Linear Core in an analogous way, with $\pi$ for the multlipicity meta-variable and $\Delta$ due to the usage environment technique. We will clarify this in the text.

> 345, The phrase "can be readily applied to other non-strict languages" is rather a moot point, because in practical terms the only such language is Haskell. I'd suggest rephrasing along the lines of my first comment about line 107.

We agree this is a better positioning of the work (thanks!) and will revise accordingly.

> 927, Explain why "gets struck" is an appropriate way to deal with a bad use of a linear variable, e.g. that this is a standard semantic way of dealing with badly-formed terms, such as trying to add two values that are not numbers.

Will revise accordingly.

> 1079, Clean should also be included in related work, as it has a non-strict semantics, and uses uniqueness types to ensure that resources are used at most once.

Thank you for the reference. We will include it in our revision.

### Reviewer C

> The result is incremental.

Our work opens up new avenues of research: in a more applied sense, enabling linearity-aware Core-to-Core transformations; in a more conceptual sense, the study of linearity-aware intermediate representations for non-strict language features.
As stated in **Overview (a)**, our work provides a conceptual framework and prototype implementation that addresses a long standing problem in the (internals of the) implementation of Linear Haskell.

> The paper doesn't address coercions (which seems like table stakes for a Core
> type system), nor bring the laziness-aware features back to the surface level
> of Linear Haskell.
> What does the GHC plugin do on coercion terms if they are not supported in
> the theory? Do coercions not come up in Linear Haskell programs?

Equality coercions in Core exist to support advanced type-level features
(e.g. type families, GADTs) which are mostly orthogonal to the mismatch between
"naive" syntactic and semantic linearity. So we do not model them at this stage to 
illustrate the essence of our system without the added complexity of coercions. 
As discussed in Section 6.1 (L.1141), there are plausible interactions between 
GADTs and linearity through so-called multiplicity coercions. We expect
that our system can scale to such a setting, but we believe that the formalization
of such coercions is an independent topic of study.

In our prototype implementation casts and coercions are essentially ignored. 
Our plugin will reject programs which depend on coercions to be accepted as linear.

> The evaluation is fairly light. (Perhaps there just are a large number of Linear Haskell programs to draw from?)
> Are there other significant Linear Haskell programs beyond the three libraries evaluated in the paper?

We chose the codebases in question due to a combination of size and real-world utility (e.g. `linear-base` is used by effectively most Linear Haskell programs). While other codebases that use Linear Haskell exist, they are often not pure Haskell codebases (e.g. the `inline-java`, `jni` and `jvm` projects), which makes it challenging to pass them through our tool or are too small to provide meaningful information.

> The result has fairly narrow applicability: IRs for lazy linearly typed languages.

As pointed out in **Review B**, our work applies beyond IRs for lazy linear languages (i.e. Core and Haskell). 
Conceptually these issues arise in any languages that feature non-strict features (e.g. streams, lazy evaluation via libraries, etc.) and so our work can be seen to apply to linear extensions of such languages. We plan to reposition our motivations accordingly.

> Do you have any sense of what the improvement would be if compared against a baseline syntactic linear type system for Core, i.e. Bernardy, et al. but for Core?

A baseline syntactic linear type system for Core would essentially reject too many reasonable programs.
See **Overview (a)**.

> The citation for Bernardy et al. 2017 should probably be to the POPL'18 version of the paper rather than the arXiv preprint.

We will cite both in our revision, given that the linearity-aware operational semantics can only be found in the long-form version.