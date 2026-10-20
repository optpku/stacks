/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_30_1_Separation
public import stacks_project.Chap88.Definition_88_20_1
public import stacks_project.Chap88.Definition_88_21_1
public import stacks_project.Chap88.Lemma_88_22_1

/-!
# Lemma 88.22.2

A locally Noetherian formal algebraic space locally of finite type over a
complete discrete valuation ring, whose relative diagonal is both rig-étale
and rig-surjective, has flat locus isomorphic to the formal spectrum or empty.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Lemma 88.22.2: let `X` be a locally Noetherian formal algebraic space which
is locally of finite type over a complete discrete valuation ring `A`. Let
`X' ⊂ X` be the flat locus of Lemma 88.22.1, realized as `flatLocus p` with
closed immersion `flatLocusι p`. If the relative diagonal
`diagonal p : X ⟶ pullback p p` is rig-étale and rig-surjective, then
`flatLocusι p ≫ p` is an isomorphism, or else every section of `flatLocus p`
is empty. -/
@[stacks 0GD9]
theorem flatLocus_eq_spf_or_empty {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    (hA : Spec (.of A) ⟶ S) {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (p : X ⟶ spf A hA)
    [LocallyOfFiniteType p] [HasPullback p p]
    [IsFormalAlgebraicSpace (pullback p p)] [IsLocallyNoetherian (pullback p p)]
    [LocallyOfFiniteType (diagonal p)] [RigEtale (diagonal p)]
    [RigSurjective (diagonal p)] :
    IsIso (flatLocusι p ≫ p) ∨ ∀ T : (Over S)ᵒᵖ, IsEmpty ((flatLocus p).obj T) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
