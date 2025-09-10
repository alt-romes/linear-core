# Semantic Linearity in a Lazy Optimising Compiler: Type-checking Linearity in GHC Core

## POPL '26 Paper 572 -- Author Response

We would like to thank the reviewers for their reviews.

Following the Chair's instructions, our reply is in three parts:

1. Overview -- summary of key points
2. Change List -- our proposed revisions
3. Detailed Response -- explicit answers to each reviewer's questions

---

## 1. Overview

### (a) Design tradeoffs viz. adapting transformation passes and simplifying Linear Core / comparing against a baseline syntactic linear type system for Core.

> **Reviewer A**: Step back and explain the design tradeoffs. Could you have done some more work to adapt the transformation passes and simplify the design of Linear Core?
> **Reviewer C**: Do you have any sense of what the improvement would be if compared against a baseline syntactic linear type system for Core, i.e. Bernardy, et al. but for Core?

[Dar uns toques -- requer nao aplicar as transformacoes / produzir resultados muito ineficientes(?) e muito irregular
 com muitos casos especiais ]

The Linear Haskell implementation in GHC originally tried to adapt the transformation passes to potentially simplify the design of a linearity-aware Core. Unfortunately, conforming the transformations to a simple syntactic linearity often meant being more restrictive, which in turn regressed the runtime performance of programs significantly. A few years later, all the linearity-related special cases in transformations ended up being removed. 

From the GHC source code and issues (e.g. https://gitlab.haskell.org/ghc/ghc/-/issues/22123), noting that linting linearity is the internal terminology for checking for linearity:
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
We will reference this in our revision.

### (b) Key ideas of Linear Core 

> **Reviewer B**: What are the key ideas that make your core language work? Are there new ideas involved, or is it a combination of existing ideas?

[TODO - Reiterar, apontando para o paper, dizer que se vai melhorar]

### (c) Semantic notion of linearity

> **Reviewer A**: you are not defining a semantic notion of linearity. Rather, you're designing a typing discipline which fits the lazy semantics of linearity.

We concur that we are not defining a (new) notion of semantic linearity. Indeed, our definition is a sharpened version adapted/refined/imported of that of Linear Haskell and our work establishes a new syntactic definition of linearity that is more precise wrt the semantic notion. We thank the reviewer for this perspective and we plan to rewrite our positioning accordingly.

### (d) Linearity in the presence of exceptions

> **Reviewer A**: One of the main criticism of Linear Haskell is that it does not preserve linearity in the presence of exceptions.

[TODO]

1) Library-level treatment of exceptions that preserve linearity. Indeed LH does nothing about it.
2) There is no explicit representation of exceptions in Core.
3) Transformation preserve exceptions(?) -- IMO this is is unfixable without major rework of the exception system. 


## 2. Change List

We will address all of the points raised by the reviewers:

- Revise introductory examples to more adequately flesh out the relevant points (**Reviewer A**).
- Revise the paper title and abstract, emphasizing the more general contributions (**Reviewer B**):
    [Tentative titles: Checking Semantic Linearity in a Non-strict Optimising Compiler / 
                       Checking Linearity in Non-strict Languages /
                       Checking Semantic Linearity in a Non-strict Optimising Compiler]
- Revise introduction to more clearly flesh out key ideas, contributions, target audience and relationship
  with semantic linearity (**Reviewer A, B, C**).
- Expand evaluation with more codebases that rely on Linear Haskell (**Reviewer C**).
- Address all minor corrections and presentation issues raised by the reviewers, expanding explanations
as requested (**Reviewer A, B and C**).

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

[TODO]

> “Γ, 𝑥:Δ 𝜎; Δ ⊢ 𝑥 : 𝜎”: I'm guessing that the two occurrences of Δ refer to different things. Clarify or repair.

Our goal with this notation is to assert that the usage environment associated with variable `x` is Δ, which consists exactly of all ambient linear variables which are tracked by context Δ. The two Δ are indeed the same.
We will clarify this in our revision.

> Fig 4. “CaseWHNF”: this rule is unparseable for me. 

[TODO] Add explanation.
We will fix the type-setting issue (**Change list**).

> Fig 4. The Last judgement has 6 or 7 argument and I don't know how many fixed parts.

We will fix the type-setting issue (**Change list**).

> Inference of usage environments for recursive lets.

[TODO -- Responder que sim. Clarificar a quest'ao do Delta que o reviewer nao percebeu]

> Perhaps there should be a discussion of whether doing "case" on a WHNF expression is useful at all. I guess this is motivated by practical considerations, please spell them out at this point.

Case-ing on a WHNF arises frequently due to the optimizing transformations. We will further emphasize this at this point in the paper, noting that this discussion is present in L. [TODO].

> - “we must branch on weak head normal formed-ness to accurately type expression”: -> accurate typing of case expressions depends on whether the scrutinee is in WHNF.

See **Change list**.

> Clarify Γ[Δ/x], and Γ[𝑥/[Δ]]
> “𝑥: [Δ]”: At this point I realize that I don't understand the difference between Δ and [Δ]. Did I miss something? If so a back-reference to the explanation would help.

[TODO Rodrigo] Spell out what it means.
The introduction of the bracket notation is given in L.[TODO]. We will revise accordingly to make this more upfront.

> “Proof irrelevant”: I was already confused by this term earlier (what are proofs here? does this mean simply unused?) But the repeated use of "proof" in this paragraph makes me very confused.

Proof irrelevant variables cannot be used. The terminology is borrowed from proof theory (cite [TODO]), but we understand this might be confusing and does not line up exactly with the proof theoretic construction. We will revise this terminology to simply "irrelevant" and clarify its meaning. 

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

> 330, Explain the rationale for the choice of superscript and subscript on the linear calculus dubbed LinearCore.

[TODO] Inspirado pelo LH

> 345, The phrase "can be readily applied to other non-strict languages" is rather a moot point, because in practical terms the only such language is Haskell. I'd suggest rephrasing along the lines of my first comment about line 107.

We agree this is a better positioning of the work (thanks!) and will revise accordingly.

> 927, Explain why "gets struck" is an appropriate way to deal with a bad use of a linear variable, e.g. that this is a standard semantic way of dealing with badly-formed terms, such as trying to add two values that are not numbers.

Will revise accordingly.

### Reviewer C

> The result is incremental.

[TODO opens up...] 

> The paper doesn't address coercions (which seems like table stakes for a Core type system), nor bring the laziness-aware features back to the surface level of Linear Haskell.
> What does the GHC plugin do on coercion terms if they are not supported in the theory? Do coercions not come up in Linear Haskell programs?

[TODO Rodrigo] Referenciar related work.

> The evaluation is fairly light. (Perhaps there just are a large number of Linear Haskell programs to draw from?)
> Are there other significant Linear Haskell programs beyond the three libraries evaluated in the paper?

Escolhemos as maiores/mais interessantes/real world. Nem todas sao pure haskell ou grandes o suficientes (JVM blabla)
There are several codebases that depend on `linear-base` and therefore rely on linear types. 
[TODO].

> The result has fairly narrow applicability: IRs for lazy linearly typed languages.

As pointed out in **Review B**, our work applies beyond IRs for lazy linear languages. Conceptually these issues arise in 
any languages that feature non-strict features (e.g. streams, lazy evaluation via libraries, etc.) and so our work can be
seen to apply to linear extensions of such languages. We plan to reposition our motivations accordingly.


> Do you have any sense of what the improvement would be if compared against a baseline syntactic linear type system for Core, i.e. Bernardy, et al. but for Core?

A baseline syntactic linear type system for Core would essentially reject too many reasonable programs.
See **Overview (a)**.

> The citation for Bernardy et al. 2017 should probably be to the POPL'18 version of the paper rather than the arXiv preprint.

We will cite both in our revision, given that the linearity-aware operational semantics can only be found in the long-form version.


---
# RevA "Points"

- Step back and explain the design tradeoffs. Could you have done some more work to adapt the transformation passes and simplify the design of Linear Core?
- The statement of contributions should be rewritten, and the abstract adapted. See below, but in short, you are not defining a semantic notion of linearity. Rather, you're designing a typing discipline which fits the lazy semantics of linearity. (In fact, you may delete this formulaic part of the paper, the abstract is sufficient in your case.)
- Introductory examples should be chosen better. If you're not going to use a variable at all, you can simply give it multiplicity zero and solve some of the problems suggested. So this is what the reader will gravitate towards mentally instead of forming an intuition for the issue that you're actually addressing.
- the paper could do a better job at shedding a clear light on its obscure corners
- Please don't omit relative pronouns. Doing so makes reading the paper much harder. Write "[Type systems] guarantee that (linear) resources are used exactly once".

- Revise intro example to have occurrences.

- You have a new syntactic (ie. static) definition of linearity which is more flexible and thus supports more programs which are correct according to the semantic definition of linearity given by Linear Haskell.

- One of the main criticism of Linear Haskell is that it does not preserve linearity in the presence of exceptions. IMO this is is unfixable without major rework of the exception system. However it is definitely salient for something as practically minded as Core-to-Core transformations. You should clarify the situation in the introduction.

- Revise examples

- “conservatively treating all multiplicity polymorphic functions as linear,”: Is this really "conservative"? My intuition is that depending on the polarity of the occurrence of the multiplicity variable, you may have a non-conservative (ie. unsound) behavior. You must explain.

- “Γ, 𝑥:Δ 𝜎; Δ ⊢ 𝑥 : 𝜎”: I'm guessing that the two occurrences of Δ refer to different things. Clarify or repair. (Reading further down: IIUC Δ is just a terminal symbol in the syntax. It is very confusing to have it both as a terminal and a metasyntactic variable. You must change this.)

- Fig 4. “CaseWHNF”: this rule is unparseable for me. (“Γ; Δ ⊩ 𝑒 : 𝜎 ⋗ Δ𝑖”: This part is floating about have an horizontal line. Fix this.)

- Fig 4. The Last judgement has 6 or 7 argument and I don't know how many fixed parts. It would help to visually/typographically distinguish it, or some of its crucial or most unusual parts, so that it can be parsed more easily when it occurs in the rules.

- Clarify on inference of usage environments for recursive lets.

-  Perhaps there should be a discussion of whether doing "case" on a WHNF expression is useful at all. I guess this is motivated by practical considerations, please spell them out at this point.

- “Branching on WHNF-ness”: because a case expression is about "branching" already, please use another word (or remove "Branching" altogether in the title) to avoid confusion.

- “we must branch on weak head normal formed-ness to accurately type expression”: -> accurate typing of case expressions depends on whether the scrutinee is in WHNF.

- Clarify Γ[Δ/x], and Γ[𝑥/[Δ]]

- “𝑥: [Δ]”: At this point I realize that I don't understand the difference between Δ and [Δ]. Did I miss something? If so a back-reference to the explanation would help.

- Lemma 4.3: “𝑥:· 𝜎”: there is a minuscule dot here. Not the clearest typography.

- “Proof irrelevant”: I was already confused by this term earlier (what are proofs here? does this mean simply unused?) But the repeated use of "proof" in this paragraph makes me very confused.

- “The Irrelevance lemma witnesses the soundness of typing a case alternative with proof irrelevant resources with respect to typing the same expression with arbitrary resources.”: This is not very informative. Please use a more direct language, for instance: "if a case alternative is well-typed with `irrelevant' resources, then it is well-typed with arbitrary resources." (Is this correct? I don't know! Please be more clear so I would know reading the paper.)

- “Fig. 8.”: Please make this look more like a table. There should be a space between rows so that the 2-line transformations are more recognizable as such. I would suggest that you only list the transformations which were problematic. (For instance β-reduction should be completely OK with the naive system; if not explain why.)
“Linear Core is not syntax-directed.”: I thought it would be better if it would be. Please state here the design tradeoffs.
Page 22

- “in light of the flexible evaluation strategy used by optimizing compilers.”: What does this mean? Would the sentence mean something different if this phrase was removed?

- “conservatively rejects it”: -> “conservatively rejects them”:

-  “Several other works”: fix for work being uncountable.

- “Linearity-influenced optimisations.”: You could be more explicit and state that Linear Core opens the door to linearity-directed optimisations in the pipeline.

- many works”: ibid. and more occurrences below.

- “Encoding multiplicities as types allows Haskell programs to leverage features available for types to naturally extend to multiplicities as well.”: Awkward phrasing

- “Optimisations leveraging linearity.”: This paragraph is largely redundant with that in related work. I suggest you remove it to make room for more detailed explanation of the technical parts.

- “Linear Core in the Glasgow Haskell Compiler.”: Likewise, this could be elided.


# Rev B Points

- What are the key ideas that make your core language work?


- 1, The title needs further work. The present version seems to be trying to say that the approach is both general (the main title) and specific (the subtitle), but doesn't read well. I'd suggest going for a simpler and more direct title that doesn't try to cover two bases at the same time.

- 6, The first paragraph of the abstract is a bit verbose and could be compressed quite a bit. After doing so it probably makes sense to make the abstract a single paragraph.

- 107, Explain who the paper is targeted at, e.g. what kind of knowledge and experience is required. It is also important to clarify here that while Haskell is the focus of the paper, the ideas can potentially be applied to any language with non-strict features, even if the language itself is strict.

- 107, The paper contains an appendix with 28 pages of material, whereas the call for papers states that each paper should have no more than 25 pages of text, excluding bibliography. Any additional material should be included as supplementary material separate from the main paper, rather than as an appendix.

- 115, There are a lot of parenthetical remarks in the paper, which are quite distracting. It would be beneficial to try and minimise the use of this feature.

- 137, Why are two different colours (yellow and orange) used for programs that are semantically linear but not linear in Core?

- 330, Explain the rationale for the choice of superscript and subscript on the linear calculus dubber LinearCore.

- 345, The phrase "can be readily applied to other non-strict languages" is rather a moot point, because in practical terms the only such language is Haskell. I'd suggest rephrasing along the lines of my first comment about line 107.

- 927, Explain why "gets struck" is an appropriate way to deal with a bad use of a linear variable, e.g. that this is a standard semantic way of dealing with badly-formed terms, such as trying to add two values that are not numbers.

- 1079, Clean should also be included in related work, as it has a non-strict semantics, and uses uniqueness types to ensure that resources are used at most once.

# Rev C Points

- Incremental.
- Coercions
- Evaluation is light
- Narrow applicability.

- What does the GHC plugin do on coercion terms if they are not supported in the theory? Do coercions not come up in Linear Haskell programs?

- Are there other significant Linear Haskell programs beyond the three libraries evaluated in the paper?

- Do you have any sense of what the improvement would be if compared against a baseline syntactic linear type system for Core, i.e. Bernardy, et al. but for Core?

# All Reviews

## Review A

Overall merit

B. OK paper, but I will not champion it
Reviewer expertise

X. Expert
Paper summary

The optimisation passes done by GHC do not preserve linearity as traditionally conceived. This problem has standing since the inception of Linear Haskell, and prevents leveraging linearity at runtime. This paper solves the problem by proposing a linear typing discipline, more suited to lazy languages. A key idea is that some variables may act as aliases to others. Such aliasing is recorded in the context, so that using such an alias is equivalent to using what it corresponds to. Further care need to be taken to account case analysis, which may or may not correspond to resource consumption.

Still, there is some significant improvement to be made:

    Present the work better in context:
        Step back and explain the design tradeoffs. Could you have done some more work to adapt the transformation passes and simplify the design of Linear Core?
        The statement of contributions should be rewritten, and the abstract adapted. See below, but in short, you are not defining a semantic notion of linearity. Rather, you're designing a typing discipline which fits the lazy semantics of linearity. (In fact, you may delete this formulaic part of the paper, the abstract is sufficient in your case.)
    Introductory examples should be chosen better. If you're not going to use a variable at all, you can simply give it multiplicity zero and solve some of the problems suggested. So this is what the reader will gravitate towards mentally instead of forming an intuition for the issue that you're actually addressing.
    Some surface cleanup and/or clarification of the design (see details below, but mostly the case analysis rule should be given more care.)

Rationale for assessment: As such it solves a practical problem by attacking it head on, and allows for a new line of research to develop. This is a very good point. Even if the main idea comes through soundly, unfortunately, the design of the type system is very involved, and the paper could do a better job at shedding a clear light on its obscure corners. Similar expositions of complex designs of GHC have been published in top PL conferences before, and arguably are necessary to advance the field. As for the question of whether the design could be simplified. Even though there may be a superior alternative, as an expert I do not see an obvious candidate.

Comments for authors

Abstract

“[Type systems] guarantee (linear) resources are used exactly once”: Please don't omit relative pronouns. Doing so makes reading the paper much harder. Write "[Type systems] guarantee that (linear) resources are used exactly once".

“We prove Linear Core is sound”: another occurrence. The last one that I point out.
1 Introduction

“let 𝑦 = free 𝑥 in free 𝑥”: I am underwhelmed by this example. Because y has zero occurrence, the free variables bound in its definition really count as no occurrence, for many type-systems with (bounded) linearity. This includes for instance the (otherwise flawed) system by McBride from a while back.
Page 2

“We introduce the concept of semantic linearity,”: the definition of linearity in the Linear Haskell paper is based on "consumed exactly once", which is a semantic notion. The phase semantics in Girard 86 captures a semantic notion of linearity. So you are most definitely not introducing the concept of semantic linearity. At first reading, I do not know if your definition is novel, but you must qualify this sentence or remove it.

(When reaching Sec. 3.2, I understand what you mean. You have a new syntactic (ie. static) definition of linearity which is more flexible and thus supports more programs which are correct according to the semantic definition of linearity given by Linear Haskell.

Arguably this distinction is petty, but I don't know anyone who counts a type-system as a semantics, so if you don't want to confuse readers you must go with my advice.)
Page 3

“this is the first type system to capture linearity semantically in this context”: The Linear Haskell paper has an operational semantics which captures linearity. So you must be more careful here as well.

One of the main criticism of Linear Haskell is that it does not preserve linearity in the presence of exceptions. IMO this is is unfixable without major rework of the exception system. However it is definitely salient for something as practically minded as Core-to-Core transformations. You should clarify the situation in the introduction.
2 Linearity, Semantically
Page 3

“f handle = let x = close handle in handle”:

Here, "close handle" does not occur syntactically in any control flow path. This is the same bad example as above. This does not mean that the general remark is invalid, but I remain unconvinced at this point.

“conditionally needed at runtime, depending on the branch taken.”: This example is more convincing, good!
Page 4

“syntactic occurrence of a variable isn’t enough to determine whether it is used.”: A bad explanation supported by a bad example. Here, z has no occurrence.
Page 5

“we must infer”: Here you're conflating inference and checking. IMO for a core language you'd be better of having explicit declarations rather than having to infer complex conditions.
3 A Type System for Semantic Linearity in Core
Page 7

“that we prove is sound”: "that we prove to be sound"
Page 8

““proof irrelevance””: perhaps you mean variables with zero occurrences? In any case, this phrase in quotes does not help.

“a set of the data constructors”: drop "the"
Page 9

Fig. 3: “𝜌” for patterns makes me stumble, especially when you already have σ for types. In general the use of Greek letters is somewhat random. (eg. ϕ,σ for types instead of a more alphabetic σ,τ, etc.) This may seem petty, but the formalities are dense enough, the paper does not need extra surprises.

“conservatively treating all multiplicity polymorphic functions as linear,”: Is this really "conservative"? My intuition is that depending on the polarity of the occurrence of the multiplicity variable, you may have a non-conservative (ie. unsound) behavior. You must explain.
Page 10

“Γ, 𝑥:Δ 𝜎; Δ ⊢ 𝑥 : 𝜎”: I'm guessing that the two occurrences of Δ refer to different things. Clarify or repair. (Reading further down: IIUC Δ is just a terminal symbol in the syntax. It is very confusing to have it both as a terminal and a metasyntactic variable. You must change this.)

In figure 4:

    “CaseWHNF”: this rule is unparseable for me. (“Γ; Δ ⊩ 𝑒 : 𝜎 ⋗ Δ𝑖”: This part is floating about have an horizontal line. Fix this.)

    The Last judgement has 6 or 7 argument and I don't know how many fixed parts. It would help to visually/typographically distinguish it, or some of its crucial or most unusual parts, so that it can be parsed more easily when it occurs in the rules.

3.3 Usage environments

It is becoming very clear what the key idea is. Good.
Page 11

“𝑓 = 𝜆𝑥:1𝜎. 𝜆𝑦:1𝜎. let 𝑢 {𝑥:1 𝜎,𝑦:1 𝜎 } = (𝑥, 𝑦) in 𝑒”: So here Δ is instantiated to a concrete usage environment? What is Δ???
Page 12

“We present our system and meta-theory agnostically to the challenge of inferring this linear typing environment by assuming recursive let expressions are annotated with the correct typing environment.”: Your formulation is opaque. Please use more plain language. Do you simply mean that if one writes the annotations then it suffices to check them? If Δ is a terminal, then you actually need inference (not a great design for a core language IMO, but again you may have practical considerations). If not, your version of core actually have those explicit, so all is good. I appears that you have considered both designs but the paper isn't consistent; or it confused me in this regard.
Page 13

“Γ; Δ ⊩ 𝑒 : 𝜎 ⋗ Δ𝑖”: That is heavyweight, but I can see it working. Perhaps there should be a discussion of whether doing "case" on a WHNF expression is useful at all. Why can't the body (the branches) use the arguments of the constructor directly? IIUC this is equivalent under lazy evaluation, and it is the whole point of the argument. I guess this is motivated by practical considerations, please spell them out at this point.

“Branching on WHNF-ness”: because a case expression is about "branching" already, please use another word (or remove "Branching" altogether in the title) to avoid confusion.

“we must branch on weak head normal formed-ness to accurately type expression”: -> accurate typing of case expressions depends on whether the scrutinee is in WHNF.
Page 14

Line 642, in the 3rd premiss of CaseWHNF, z appears on to“𝑒 ′ :𝑧 𝜎 ⇒ 𝜑”:
4 Metatheory of Linear Core
Page 18

“Lemma 4.1”: I'm confused by the informal statement. If you have x:₁σ, the you must consume x exactly once. Instead, you replace it by x :Δ δ, so there is now a disjunction. You must add Δ to the linear context. I believe that this is what you're doing in the formal statement, but I'm confused by Γ[Δ/x]. What is that supposed to do? I'm normally reading this as substitute Δ for x in Γ, but that does not seem to make sense here.

“Γ[𝑥/[Δ]]”: I have no idea what this could mean.

“𝑥: [Δ]”: At this point I realize that I don't understand the difference between Δ and [Δ]. Did I miss something? If so a back-reference to the explanation would help.

Lemma 4.3: “𝑥:· 𝜎”: there is a minuscule dot here. Not the clearest typography.

“Proof irrelevant”: I was already confused by this term earlier (what are proofs here? does this mean simply unused?) But the repeated use of "proof" in this paragraph makes me very confused.

“The Irrelevance lemma witnesses the soundness of typing a case alternative with proof irrelevant resources with respect to typing the same expression with arbitrary resources.”: This is not very informative. Please use a more direct language, for instance: "if a case alternative is well-typed with `irrelevant' resources, then it is well-typed with arbitrary resources." (Is this correct? I don't know! Please be more clear so I would know reading the paper.)
Page 20

“Fig. 8.”: Please make this look more like a table. There should be a space between rows so that the 2-line transformations are more recognizable as such. I would suggest that you only list the transformations which were problematic. (For instance β-reduction should be completely OK with the naive system; if not explain why.)
5 Linear Core as a GHC Plugin
Page 21

“Linear Core is not syntax-directed.”: I thought it would be better if it would be. Please state here the design tradeoffs.
Page 22

“in light of the flexible evaluation strategy used by optimizing compilers.”: What does this mean? Would the sentence mean something different if this phrase was removed?

“conservatively rejects it”: -> “conservatively rejects them”:
6 Related and Future Work
Page 23

“Several other works”: fix for work being uncountable.

“Linearity-influenced optimisations.”: You could be more explicit and state that Linear Core opens the door to linearity-directed optimisations in the pipeline.

“many works”: ibid. and more occurrences below.
Page 24

“Encoding multiplicities as types allows Haskell programs to leverage features available for types to naturally extend to multiplicities as well.”: Awkward phrasing

“Optimisations leveraging linearity.”: This paragraph is largely redundant with that in related work. I suggest you remove it to make room for more detailed explanation of the technical parts.

“Linear Core in the Glasgow Haskell Compiler.”: Likewise, this could be elided.

## Review B

Overall merit

A. Good paper, I will champion it
Reviewer expertise

Y. Knowledgeable
Paper summary

This paper presents a typed core language for Haskell that takes account of semantic linearity in the presense of laziness. The type system is proved sound and to ensure linearity, and its utility is demonstrated in practice using various optimising transformations and real-world library code.
Comments for authors

General comments:

Linear types are a tantalisingly appealing idea, but have proved notoriously challenging in practice. This paper makes a impressive new contribution in the context of Haskell, by developing the theory and practice of a linear core language that takes account of the additional, significant complexities that arise from the use of non-strict evaluation.

While the paper uses Haskell, many modern languages include non-strict features, and the use of resource types such as linear types is becoming increasingly popular, so this work also has the potential to be more widely applicable.

Overall, this is an excellent piece of work that makes a significant contribution to both the theory and practice of linear type systems, and merits being published in POPL.

Specific comments:

1, The title needs further work. The present version seems to be trying to say that the approach is both general (the main title) and specific (the subtitle), but doesn't read well. I'd suggest going for a simpler and more direct title that doesn't try to cover two bases at the same time.

6, The first paragraph of the abstract is a bit verbose and could be compressed quite a bit. After doing so it probably makes sense to make the abstract a single paragraph.

107, Explain who the paper is targeted at, e.g. what kind of knowledge and experience is required. It is also important to clarify here that while Haskell is the focus of the paper, the ideas can potentially be applied to any language with non-strict features, even if the language itself is strict.

107, The paper contains an appendix with 28 pages of material, whereas the call for papers states that each paper should have no more than 25 pages of text, excluding bibliography. Any additional material should be included as supplementary material separate from the main paper, rather than as an appendix.

115, There are a lot of parenthetical remarks in the paper, which are quite distracting. It would be beneficial to try and minimise the use of this feature.

132, I very much appreciate starting off with a series of examples to illustrate the problems this paper addresses. Spending four pages on this is quite a lot, but the examples illustrate different points and are very helpful.

137, Why are two different colours (yellow and orange) used for programs that are semantically linear but not linear in Core?

330, Explain the rationale for the choice of superscript and subscript on the linear calculus dubber LinearCore.

345, The phrase "can be readily applied to other non-strict languages" is rather a moot point, because in practical terms the only such language is Haskell. I'd suggest rephrasing along the lines of my first comment about line 107.

927, Explain why "gets struck" is an appropriate way to deal with a bad use of a linear variable, e.g. that this is a standard semantic way of dealing with badly-formed terms, such as trying to add two values that are not numbers.

1079, Clean should also be included in related work, as it has a non-strict semantics, and uses uniqueness types to ensure that resources are used at most once.
Specific questions to be addressed in the author response

    What are the key ideas that make your core language work?

Are there new ideas involved, or is it a combination of existing ideas? Either is fine, but it's important for the key ideas to explicitly identified and discussed in the paper, rather than just presenting the core language and showing that it works.

## Review C

Overall merit

B. OK paper, but I will not champion it
Reviewer expertise

Y. Knowledgeable
Paper summary

This paper introduce Linear Core, a linear type system for GHC's Core intermediate language (minus coercions) that eschews standard syntactic notions of linearity in favor of a more refined approach that takes into account the lazy semantics of GHC Core and is thereby able to type more programs that are semantically linear. The paper provides many examples of semantically but not syntactically linear programs (and some syntactically but not semantically ones as well) and shows how these programs naturally arise during GHC rewriting. Under the current Core typing rules, such programs would be considered ill-typed, so linearity checking is simply not done past the first phase of compilation.

The defines an operational semantics that accounts for (affine) linearity checking such that a resource gets stuck if a linear resource is used more than once. This gives an operational account of non-duplication. A type soundness result shows, in the usual way, that well-typed programs don't get stuck, and those Linear Core programs can never duplicate resources. A GHC plugin is developed and evaluated on three Linear Haskell libraries including the substantial linear-base library. The results show that the system is flexible enough to preserve linear typability across many rewrites done by GHC.
Comments for authors

Strengths:

    The paper is very well written and clear.

    The formal claims are precisely stated and appear correct.

    The result gives a refinement of Bernardy et al.'s Linear Haskell type system that is robust with respect to lazy semantics and adapted to Core.

Weaknesses:

    The result is incremental.

    The paper doesn't address coercions (which seems like table stakes for a Core type system), nor bring the laziness-aware features back to the surface level of Linear Haskell.

    The evaluation is fairly light. (Perhaps there just are a large number of Linear Haskell programs to draw from?)

    The result has fairly narrow applicability: IRs for lazy linearly typed languages.

Overall, I don't have any technical issues with the paper. I think the ideas for making the type system understand linearity semantically in the presence of laziness are good. The evaluation provides evidence that the approach works and was able to both confirm and refute linearity preservation of GHC, while having very few cases of conservatively rejecting linear programs. My main concern is on the significance, which seems limited.

Small:

The citation for Bernardy et al. 2017 should probably be to the POPL'18 version of the paper rather than the arXiv preprint.
Specific questions to be addressed in the author response

What does the GHC plugin do on coercion terms if they are not supported in the theory? Do coercions not come up in Linear Haskell programs?

Do you have any sense of what the improvement would be if compared against a baseline syntactic linear type system for Core, i.e. Bernardy, et al. but for Core?

Are there other significant Linear Haskell programs beyond the three libraries evaluated in the paper?
