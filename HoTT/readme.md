# Foundations of Stable Category Theory: A Formalization in Coq-HoTT

## Introduction

This repository contains a formalization of stable category theory within the framework of Homotopy Type Theory using the Coq proof assistant. The development provides a comprehensive treatment of pre-stable and stable categories through a univalent lens, culminating in a complete formalization of the duality principle that underlies stable homotopy theory. The formalization spans approximately 3,000 lines of Coq code and introduces several novel mathematical concepts that emerged during the formal development process.

## Context and Motivation

The formalization of category theory in proof assistants has seen substantial progress across multiple systems. Lean 4's mathlib contains an extensive treatment of triangulated categories developed by Joël Riou between 2023 and 2024, including shift functors, exact functors, and derived category theory. This implementation leverages Lean's classical foundations and powerful automation features to handle the complex coherence conditions inherent in triangulated structures. In parallel, the UniMath library has developed the most comprehensive category theory library built on univalent foundations, containing over 210,000 theorems. However, UniMath's focus has remained on foundational structures, and triangulated or stable categories are notably absent from its repository.

The gap between these approaches is significant. Triangulated categories are fundamentally homotopical in nature, axiomatizing phenomena from stable homotopy theory, yet existing formalizations treat them through purely algebraic means. The suspension-loop adjunction, while appearing synthetically in various HoTT libraries, has not been formalized as a categorical construction defining stability. Furthermore, the deep symmetries embodied in the duality principles of stable categories align naturally with homotopy type theory's principle that isomorphic structures are equal, suggesting that a univalent approach might yield new insights.

This formalization addresses these gaps by providing the first HoTT-based treatment of stable categories that achieves both mathematical completeness and computational tractability. The work can be viewed as extending UniMath's program to encompass stable phenomena while learning from the successes and challenges documented in other formalization efforts.

## Technical Architecture

The formalization follows a layered architecture that builds systematically from basic categorical concepts to the full theory of stable categories. At the foundation, we establish a comprehensive treatment of additive categories, beginning with zero objects and biproducts. The approach to biproducts separates structural data from universal properties, enabling computational work while maintaining the flexibility for abstract reasoning:

```coq
Record Biproduct {C : PreCategory} (X Y : object C) := {
  biproduct_obj : object C;
  inl : morphism C X biproduct_obj;
  inr : morphism C Y biproduct_obj;
  outl : morphism C biproduct_obj X;
  outr : morphism C biproduct_obj Y
}.
```

This design choice reflects lessons learned from performance challenges documented in other categorical formalizations, particularly the work of Gross, Chlipala, and Spivak, who identified dependent pattern matching and excessive reduction as primary bottlenecks in scaling categorical constructions.

Building on the additive foundation, we introduce the notion of pre-stable categories, a conceptual innovation that captures categories equipped with suspension and loop functors connected by natural transformations without requiring these functors to be equivalences:

```coq
Record PreStableCategory := {
  A :> AdditiveCategory;
  Susp : AdditiveFunctor A A;
  Loop : AdditiveFunctor A A;
  eta : NaturalTransformation 1%functor (Loop o Susp)%functor;
  epsilon : NaturalTransformation (Susp o Loop)%functor 1%functor
}.
```

This intermediate notion, absent from classical treatments, emerges naturally in the HoTT setting and provides a framework for studying categories "on their way" to becoming stable. The formalization demonstrates that pre-stable categories exhibit rich structure, including a natural hierarchy of stability conditions that we classify systematically.

## Distinguished Triangles and Triangulated Structure

The treatment of distinguished triangles represents a key technical achievement. Rather than treating triangles merely as sequences of morphisms, we introduce structured data that captures their geometric meaning and makes exactness conditions computationally checkable:

```coq
Record DistinguishedTriangle {S : PreStableCategory} := {
  triangle : Triangle;
  zero_comp_1 : (g triangle o f triangle)%morphism = 
                zero_morphism (add_zero S) (X triangle) (Z triangle);
  zero_comp_2 : (h triangle o g triangle)%morphism = 
                zero_morphism (add_zero S) (Y triangle) (object_of (Susp S) (X triangle));
  zero_comp_3 : (morphism_of (Susp S) (f triangle) o h triangle)%morphism = 
                zero_morphism (add_zero S) (Z triangle) (object_of (Susp S) (Y triangle))
}.
```

The formalization establishes the fundamental properties of distinguished triangles, including the rotation operation that transforms a triangle X → Y → Z → ΣX into Y → Z → ΣX → ΣY, and proves that rotation preserves the distinguished property. We verify the axioms TR1 and TR2 of triangulated categories, showing that every morphism extends to a distinguished triangle and that isomorphisms of triangles preserve the distinguished property.

The implementation of triangle morphisms and their categorical structure required careful attention to coherence conditions. We prove that triangles with their morphisms form a category, with composition and identity morphisms satisfying the expected laws. This development revealed subtle issues in managing equality proofs that are handled through a systematic collection of transport lemmas.

## The Duality Principle

Perhaps the most significant mathematical contribution of this formalization is the complete treatment of how stable categories behave under dualization. The opposite of a pre-stable category is constructed by reversing all morphisms while simultaneously exchanging the roles of suspension and loop functors:

```coq
Definition opposite_prestable_category (PS : PreStableCategory) : PreStableCategory := 
  Build_PreStableCategory
    (opposite_additive_category PS)
    (opposite_additive_functor (Loop PS))  (* Loop becomes Susp *)
    (opposite_additive_functor (Susp PS))  (* Susp becomes Loop *)
    (opposite_natural_transformation (epsilon PS))
    (opposite_natural_transformation (eta PS)).
```

This construction, while understood informally in the mathematical community for decades, had never been formalized previously. The formalization makes precise how every theorem about stable categories has a dual obtained by passing to the opposite category. We prove that the opposite of a proper stable category is again proper stable, with the triangle identities and isomorphism conditions transferring appropriately.

The duality principle extends to distinguished triangles, where we show how triangles in the opposite category relate to triangles in the original category with reversed morphisms and swapped suspension functors. This development required establishing numerous technical lemmas about how natural transformations and functorial constructions behave under dualization.

## Novel Mathematical Discoveries

The process of formalization led to several mathematical insights that appear to be new to the literature. Most notably, we discovered the η-zero forcing principle, which reveals unexpected rigidity in pre-stable categories:

```coq
Theorem eta_zero_forcing_principle :
  forall (PS : PreStableCategory) (X : object PS),
  (exists (i : morphism PS (@zero _ (add_zero PS)) X) 
          (r : morphism PS X (@zero _ (add_zero PS))),
    (r o i)%morphism = 1%morphism) →
  components_of (eta PS) X = zero_morphism ... →
  components_of (eta PS) (@zero _ (add_zero PS)) = zero_morphism ...
```

This theorem establishes that if any object admits a retraction from the zero object and the unit transformation η vanishes at that object, then η must also vanish at the zero object itself. The proof leverages the uniqueness of morphisms involving zero objects in a novel way, and the result suggests deep connections between the vanishing locus of natural transformations and the retraction structure of categories.

Building on this principle, we developed a classification of pre-stable categories based on their stability properties. The formalization reveals that pre-stable categories naturally stratify into five distinct levels: trivial pre-stable categories where η or ε can be zero, semi-stable categories where either η or ε consists of isomorphisms, balanced categories where the isomorphism properties of η and ε are perfectly correlated, almost proper stable categories where both are isomorphisms but triangle identities may fail, and finally proper stable categories with full equivalence between suspension and loop.

## Computational Aspects

The formalization revealed several computational phenomena that suggest algorithmic applications. The identity triangle can be constructed uniformly for any object, triangle rotation preserves distinguished status through an explicit algorithm, and morphisms of triangles form a category with mechanically verifiable composition laws. The opposite construction exhibits perfect involutive behavior, with the double opposite returning to the original category up to definitional equality in many cases.

These computational aspects required careful design choices regarding opacity and reduction behavior. Following lessons from prior work, we minimize dependent pattern matching, use strategic opacity to control reduction, and separate data from properties throughout. The resulting development maintains acceptable performance even for complex proofs involving multiple triangle manipulations and functor compositions.

## Relationship to Existing Work

This formalization relates to several streams of work in formalized mathematics. The integration with the Coq-HoTT library is fundamental, as we build directly on its treatment of equivalences, univalence, and basic category theory. Our approach to universe management follows patterns established in the HoTT library, though stable categories introduce additional universe polymorphism challenges that required novel solutions.

The relationship to UniMath's category theory library is particularly relevant. Both developments share a commitment to constructive mathematics and univalent foundations, suggesting that our results could be ported to the UniMath framework. Such a port would finally provide UniMath with triangulated and stable categories, addressing a significant gap in their otherwise comprehensive library.

Comparison with Lean's triangulated category formalization reveals interesting trade-offs. While Lean achieves impressive completeness including derived categories and localization, their classical approach requires explicit tracking of isomorphisms where our univalent framework allows working up to equivalence naturally. However, Lean's superior automation and performance characteristics enable them to develop more extensive libraries of specific examples and applications.

## Applications and Extensions

The framework established here enables several immediate applications in formalized mathematics. The distinguished triangle structure provides a foundation for verified homological algebra, including long exact sequences with verified connecting homomorphisms and formal proofs of fundamental results like the five lemma in triangulated settings. The stable categorical framework opens the door to formalized stable homotopy theory, including verified constructions of stable homotopy groups and formal treatments of spectral sequences.

Looking forward, this work provides essential infrastructure for formalizing stable ∞-categories, which are increasingly recognized as the correct framework for stable homotopy theory. The 1-categorical foundations established here, particularly the treatment of triangulated structures and duality, provide necessary prerequisites for such a development. The formalization also suggests extensions to equivariant and motivic settings, where the interplay between stability and additional structure presents fascinating challenges for formal verification.

## Technical Implementation

The formalization comprises approximately 3,000 lines of Coq code organized into seven main modules. The development requires Coq 8.19 or later with a compatible version of the HoTT library. Building the complete formalization typically requires 8GB of RAM and takes approximately 10 minutes on modern hardware. The modular architecture enables independent development of components and facilitates extraction of subtheories for specific applications.

## Conclusion

This formalization represents a significant advance in computer-verified mathematics, providing the first comprehensive treatment of stable category theory within homotopy type theory. By combining the conceptual clarity of univalent foundations with careful attention to computational feasibility, we have created a framework that serves both theoretical exploration and practical application. The discovery of new mathematical phenomena during the formalization process demonstrates the value of formal methods not merely for verification but as a tool for mathematical discovery. As the mathematical community continues to embrace formal verification, this work provides essential infrastructure for the next generation of computer-assisted mathematics in stable homotopy theory and related fields.

---

**Author**: Charles Norton  
**Date**: June 16, 2025  
**License**: MIT  
**Citation**: Norton, C. (2025). Foundations of Stable Category Theory. Computer formalization in Coq-HoTT. Available at: [repository-url]
