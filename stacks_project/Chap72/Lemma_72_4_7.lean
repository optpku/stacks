/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap72.Lemma_72_4_7_IntegralClosed
import StacksCheckRecall

/-!
# Lemma 72.4.7

Let `S` be a scheme. Let `X` be a decent algebraic space over `S`. There are
canonical bijections between the set of points of `X`, the set of irreducible
closed subsets of `Points X`, and the set of integral closed subspaces of `X`.
The bijection from points to irreducible closed subsets sends `x` to
`closure {x}`. The bijection from integral closed subspaces to irreducible
closed subsets sends `Z` to `Z.pointsSet`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 72.4.7. For a decent algebraic space, points, irreducible closed subsets,
and integral closed subspaces are canonically in bijection. The maps to irreducible
closed subsets are singleton closure and the underlying support, respectively. -/
@[stacks 0ENF] #check (AlgebraicGeometry.AlgebraicSpace.canonicalBijections :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X],
    Function.Bijective
      (irreducibleSetEquivPoints.toEquiv.symm : Points X ≃ IrreducibleCloseds (Points X)) ∧
    Function.Bijective
      (IntegralClosedSubspaces.irreducibleClosed :
        IntegralClosedSubspaces X → IrreducibleCloseds (Points X)) ∧
    (∀ x : Points X,
      (irreducibleSetEquivPoints.toEquiv.symm x : Set (Points X)) = closure {x}) ∧
    (∀ (Z : ClosedSubspace X) (h : IsIntegral Z.X),
      (IntegralClosedSubspaces.irreducibleClosed (IntegralClosedSubspaces.mk Z h) :
        Set (Points X)) = Z.pointsSet))

#check (coe_irreducibleEquivPoints_symm_apply :
  ∀ {α : Type u} [TopologicalSpace α] [QuasiSober α] [T0Space α] (x : α),
    (irreducibleSetEquivPoints.toEquiv.symm x : Set α) = closure {x})

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ofIrreducibleClosed_spec :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (T : IrreducibleCloseds (Points X)),
    IsIntegral (ClosedSubspace.ofIrreducibleClosed T).X ∧
      (ClosedSubspace.ofIrreducibleClosed T).pointsSet = (T : Set (Points X)))

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.coe_irreducibleClosed :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X) [IsIntegral Z.X],
    (Z.irreducibleClosed : Set (Points X)) = Z.pointsSet)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.existsUnique_hom_ofIrreducibleClosed :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (Z : ClosedSubspace X) [IsIntegral Z.X],
    ∃! f : Z.X ⟶ (ClosedSubspace.ofIrreducibleClosed Z.irreducibleClosed).X,
      f ≫ (ClosedSubspace.ofIrreducibleClosed Z.irreducibleClosed).ι = Z.ι)

end AlgebraicGeometry.AlgebraicSpace
