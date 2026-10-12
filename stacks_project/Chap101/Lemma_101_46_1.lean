/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap101.Lemma_101_46_1_FiniteComponents

/-!
# Finite irreducible components on compact opens of algebraic stacks

Lemma 101.46.1 records the smooth-atlas characterizations of the property that an
algebraic stack has finitely many irreducible components on compact opens, including
the algebraic-space and quasi-compact stack tests.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace HasFiniteIrreducibleComponentsOnCompactOpens

/-- Lemma 101.46.1: let `X` be an algebraic stack. The following are equivalent:
there is a surjective smooth morphism `U ⟶ X` where `U` is a scheme such that every
quasi-compact open of `U` has finitely many irreducible components; for every scheme
`U` and every smooth morphism `U ⟶ X` every quasi-compact open of `U` has finitely
many irreducible components; for every algebraic space `Y` and smooth morphism
`Y ⟶ X` the space `Y` satisfies the equivalent conditions of Morphisms of Spaces,
Lemma 67.49.1; and for every quasi-compact algebraic stack `Y` smooth over `X` the
space `Points Y` has finitely many irreducible components. -/
@[stacks 0GMI]
theorem tfae {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    List.TFAE
      [existsSurjectiveSmooth
          (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X,
        forallSmooth
          (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X,
        forallSmoothSpaceFiniteComponents X,
        finiteIrreducibleComponentsOnSmoothCompact X] :=
  sorry

end HasFiniteIrreducibleComponentsOnCompactOpens

end AlgebraicGeometry.AlgebraicStack
