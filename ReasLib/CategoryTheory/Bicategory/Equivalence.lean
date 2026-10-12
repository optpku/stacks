/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.Calculus
public import ReasLib.CategoryTheory.Bicategory.Equivalence.OnHom
public import ReasLib.CategoryTheory.Bicategory.Equivalence.Pseudofunctor
public import ReasLib.CategoryTheory.Bicategory.Equivalence.StrictPseudofunctor
public import ReasLib.CategoryTheory.Bicategory.Equivalence.ObjectProperty

/-!
# Bicategorical equivalences

Aggregate entry point for reusable bicategorical equivalence infrastructure.

New developments can import a focused leaf: `Equivalence.Calculus` for intrinsic
equivalence calculus and induced hom-category equivalences,
`Equivalence.OnHom` for adjoint-equivalence data on a fixed `1`-morphism,
`Equivalence.Pseudofunctor.Mapping` for mapping data,
`Equivalence.Pseudofunctor.Coherence` for its mate comparisons,
`Equivalence.StrictPseudofunctor` for strict preservation laws, or
`Equivalence.ObjectProperty` for closure under bicategorical equivalences.
-/
