/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Morphism.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.AffineTensorPullback

/-!
# 2-arrows from isomorphisms of affine tensor functors

If `X` is an algebraic stack with affine diagonal, then an isomorphism of the
tensor functors `fᵢ* : QCoh(O_X) ⥤ ModuleCat B` attached to two morphisms
`fᵢ : Spec(B) ⟶ X` is induced by a 2-arrow `f₁ ⟶ f₂`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

/-- Let `X` be an algebraic stack with affine diagonal. Let `B`
be a ring. Let `fᵢ : Spec(B) ⟶ X`, `i = 1, 2` be two morphisms. Let
`t : f₁* ⟶ f₂*` be an isomorphism of the tensor functors
`fᵢ* : QCoh(O_X) ⥤ ModuleCat B`. Then there is a 2-arrow `f₁ ⟶ f₂` inducing
`t`. -/
theorem exists_twoArrow_of_tensorIso
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [Groupoids.Hom.Affine (diagonal.{u + 1, u, u + 1} X)]
    {U : Over S} [IsAffine U.left]
    (f1 f2 : GroupoidsOver.slice U ⟶ X)
    (t : tensorPullback f1 ≅ tensorPullback f2)
    (ht : IsTensorNatIso t) :
    ∃ α : f1 ⟶ f2, t = tensorPullbackIso α :=
  sorry

/-- `exists_twoArrow_of_tensorIso` produces a 2-arrow `α : f₁ ⟶ f₂` whose
induced tensor-functor isomorphism is `t` componentwise. -/
theorem exists_twoArrow_of_tensorIso_spec
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [Groupoids.Hom.Affine (diagonal.{u + 1, u, u + 1} X)]
    {U : Over S} [IsAffine U.left]
    (f1 f2 : GroupoidsOver.slice U ⟶ X)
    (t : tensorPullback f1 ≅ tensorPullback f2)
    (ht : IsTensorNatIso t) :
    ∃ α : f1 ⟶ f2, ∀ M : QCoh X,
      t.hom.app M = (tensorPullbackIso α).hom.app M :=
  by
    obtain ⟨α, hα⟩ := exists_twoArrow_of_tensorIso f1 f2 t ht
    exact ⟨α, fun M ↦ congrArg (fun e ↦ e.hom.app M) hα⟩

end AlgebraicGeometry.GroupoidsOver.QCoh

