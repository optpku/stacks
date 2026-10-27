/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Algebraic

/-!
# Quasi-compact morphisms of lifted groupoid fibrations
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open AlgebraicGeometry.AlgebraicSpace.CohStack (AlgebraicStack)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

/-- A 1-morphism `f : X ⟶ Y` of algebraic stacks over `S`, in the Hom-universe
of `CohStack.toGroupoids`, is quasi-compact if every 2-fibre product against a
morphism from a quasi-compact scheme admits a smooth surjective atlas from a
quasi-compact scheme. -/
@[mk_iff]
class QuasiCompact {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- The 2-fibre product of `f` with a morphism from a quasi-compact scheme
  admits a smooth surjective scheme atlas from a quasi-compact scheme. -/
  pullback_quasiCompact {U : Over S} (y : Classifying.slice U ⟶ Y)
      [CompactSpace U.left] :
    ∃ (W : Over S)
      (p : Classifying.slice W ⟶
        CategoryTheory.TwoFibreProduct.apex.{u + 1, u, u + 1, u + 1} f y),
      Classifying.Smooth p ∧ Classifying.Surjective p ∧ CompactSpace W.left

namespace QuasiCompact

/-- The identity 1-morphism of an algebraic stack is quasi-compact. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] : QuasiCompact (𝟙 X) :=
  sorry

/-- A quasi-compact 1-morphism pulls quasi-compact scheme slices back to stacks
that admit a quasi-compact smooth surjective scheme atlas. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [QuasiCompact f]
    {U : Over S} (y : Classifying.slice U ⟶ Y) [CompactSpace U.left] :
    ∃ (W : Over S)
      (p : Classifying.slice W ⟶
        CategoryTheory.TwoFibreProduct.apex.{u + 1, u, u + 1, u + 1} f y),
      Classifying.Smooth p ∧ Classifying.Surjective p ∧ CompactSpace W.left :=
  sorry

end QuasiCompact

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
