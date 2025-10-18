# Revisions to POPL Submission 572



We thank the reviewers once again for their helpful feedback that
greatly improved the revised version of our paper.

## Overview

We have highlighted in purple all of the additions to the paper.
As per our response, we have implemented all of the items in the proposed change list.
Specifically:
 - Revised the paper title and abstract,
   emphasizing the more general nature of our contributions.
 - Revised the introductory example of Section 2 to more adequately flesh
   out the significant points.
 - Revised the introduction, more clearly fleshing out key contributions and ideas.
 - Address all minor corrections and presentation issued, expanding explanations
   as requested.


## Main Changes

- Main changes in Section 1

    We have revised much of the contributions list, in line with the reviews and our response.
    We clarified the key technical ingredients and contributions of Linear Core; the idea of the lazy semantics of linearity 
    and how our work devises a type system that is suited to that concept; and briefly discussed the 
    trade-off in complexity vs modifying the optimisation passes of GHC and the overall design philosophy of 
    our work.

- Main changes in Section 2

    We revised the initial example and its explanation, as requested.
    We have also improved the text explanations of a few of the later examples.


- Main changes in Section 3

    We have revised the introduction of the Section to reiterate the key technical ingredients of Linear Core,
relating them to the concepts and intuitions discussed in Section 2.

    We have clarified our conservative presentation of multiplicity polymorphism (adding the missing variable rule); added clarifications to Section 3.3 on usage environments and revised Figure 4 according to reviewer suggestions regarding type-setting.

    We have explained the role of usage environment annotations in recursive let bindings, as requested (Section 3.5).

    We revised "proof irrelevant" resources to "irrelevant", adjusting the nomenclature throughout the paper, and revised explanation of the CaseWHNF rule.

- Main changes in Section 4

    We have clarified the notations in Section 4.2 regarding context manipulation and irrelevant resources and
adjusted the type-setting in Figure 8.

- Main changes in Section 5

    Clarified the reasoning as to why Linear Core is not syntax-oriented and pinpointed these aspects more precisely.
 
- Main changes in Section 6

    Added note on exceptions, Linear Haskell and our work; added citation to Clean; revised paragraph with inspirations for Linear Core, which now references [Brady 2021] for 0-multiplicities and [Boyland 2003] for fractional permissions, in relation to irrelevant and tagged resources, respectively.

    Merged linearity-directed optimisations paragraph with relevant future work paragraph.

## Detailed Changes

### Reviewer A

> “let 𝑦 = free 𝑥 in free 𝑥”: I am underwhelmed by this example.

We opted to leave this example due to its simple nature as an optimizing transformation. We have revised the handle example
accordingly.

> Step back and explain the design tradeoffs. Could you have done some more work to adapt the transformation passes and simplify the design of Linear Core?

Added to end of Section 1.

> The statement of contributions should be rewritten, and the abstract adapted. See below, but in short, you are not defining a semantic notion of linearity.
> “this is the first type system to capture linearity semantically in this context”: The Linear Haskell paper has an operational semantics which captures linearity. So you must be more careful here as well.

Revised in Section 1.

> One of the main criticism of Linear Haskell is that it does not preserve linearity in the presence of exceptions.

Added note regarding exceptions to discussion of related work.

> “syntactic occurrence of a variable isn’t enough to determine whether it is used.”: A bad explanation supported by a bad example. Here, z has no occurrence.

Fixed explanation.

> “conservatively treating all multiplicity polymorphic functions as linear,”: Is this really "conservative"?

Clarified our presentation of multiplicity polymorphism in Section 3.

> “Γ, 𝑥:Δ 𝜎; Δ ⊢ 𝑥 : 𝜎”: I'm guessing that the two occurrences of Δ refer to different things. Clarify or repair.

Clarified in Section 3. Revised the variable rule to be explicit in the equality of the two contexts.

> Fig 4. “CaseWHNF”: this rule is unparseable for me.

Revised the typesetting of the rule and its explanation at the end of Section 3.6.2.

> Fig 4. The Last judgement has 6 or 7 argument and I don't know how many fixed parts.

We have revised the judgment and its type-setting.

> Inference of usage environments for recursive lets. Do you simply mean that if one writes the annotations then it suffices to check them?

Clarified in the text of the corresponding subsection.

> Perhaps there should be a discussion of whether doing "case" on a WHNF expression is useful at all. I guess this is motivated by practical considerations, please spell them out at this point.

Added.

> “Lemma 4.1”: I'm confused by the informal statement

Added explanation.

> Clarify Γ[Δ/x], and Γ[𝑥/[Δ]] “𝑥: [Δ]”: At this point I realize that I don't understand the difference between Δ and [Δ]. Did I miss something? If so a back-reference to the explanation would help.

Explained the notation.

> “Proof irrelevant”: I was already confused by this term earlier (what are proofs here? does this mean simply unused?) But the repeated use of "proof" in this paragraph makes me very confused.

Revised to Irrelevant Resources.

### Reviewer B

> What are the key ideas that make your core language work?

Added to introduction and start of Section 3.

> 1, The title needs further work.

Revised.

> 107, Explain who the paper is targeted 

Added to introduction.

> 107, The paper contains an appendix with 28 pages of material,

We now reference an extended version of the paper which will be available online.

> 115, There are a lot of parenthetical remarks in the paper

Reduced significantly.

> 137, Why are two different colours (yellow and orange) used for programs that are semantically linear but not linear in Core?

Clarified in Section 2.

> 330, Explain the rationale for the choice of superscript and subscript on the linear calculus dubbed LinearCore.

Added to Section 3.2.

> 345, The phrase "can be readily applied to other non-strict languages" 

Revised.

> 927, Explain why "gets struck" is an appropriate way to deal with a bad use of a linear variable, 

Added remark.

> 1079, Clean should also be included in related work

Added.

### Reviewer C

> The result is incremental.
> The result has fairly narrow applicability: IRs for lazy linearly typed languages

Expanded motivation and contributions in introduction.

> Do you have any sense of what the improvement would be if compared against a baseline syntactic linear type system for Core, i.e. Bernardy, et al. but for Core?

Added clarification in introduction.

> The citation for Bernardy et al. 2017 should probably be to the POPL'18 version of the paper rather than the arXiv preprint.

Fixed.