/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.TensorUnit
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.AffineTensorPullback
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.TensorFullyFaithful
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Morphism.Affine

/-! # Reconstruction of absolute morphisms from tensor functors

Symmetric tensor functors on quasi-coherent modules of Noetherian algebraic stacks
with affine diagonal are realized by affine pullback. Compatibility and uniqueness
of already given realizations are available over arbitrary base schemes.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Limits
open FiberedCategoryOver.Groupoids
open scoped Bicategory TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

/-- A natural isomorphism to affine pullback respects the canonical tensor and unit constraints. -/
def IsTensorPullbackIso {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} [IsAffine U.left]
    (F : QCoh X ⥤ ModuleCat.{u} Γ(U.left, ⊤)) [F.Monoidal]
    {f : GroupoidsOver.slice U ⟶ X} (t : F ≅ tensorPullback f) : Prop :=
  (∀ M N : QCoh X,
      (Functor.Monoidal.μIso F M N).inv ≫
          ModuleCat.ofHom
            (TensorProduct.map (t.hom.app M).hom (t.hom.app N).hom) ≫
          tensorPullback_tensorInv f M N =
        t.hom.app (Fppf.tensor M N)) ∧
    t.hom.app (structureSheaf X) ≫ (tensorPullback_unit f).hom =
      (F.mapIso (structureSheafIsoTensorUnit X) ≪≫ (Functor.Monoidal.εIso F).symm).hom

/-- Tensor-pullback compatibility is precisely the tensor equation and the structure-sheaf unit equation. -/
theorem IsTensorPullbackIso.iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {U : Over S} [IsAffine U.left]
    (F : QCoh X ⥤ ModuleCat.{u} Γ(U.left, ⊤)) [F.Monoidal]
    {f : GroupoidsOver.slice U ⟶ X} (t : F ≅ tensorPullback f) :
    IsTensorPullbackIso F t ↔
      (∀ M N : QCoh X,
          (Functor.Monoidal.μIso F M N).inv ≫
              ModuleCat.ofHom
                (TensorProduct.map (t.hom.app M).hom (t.hom.app N).hom) ≫
              tensorPullback_tensorInv f M N =
            t.hom.app (Fppf.tensor M N)) ∧
        t.hom.app (structureSheaf X) ≫ (tensorPullback_unit f).hom =
          (F.mapIso (structureSheafIsoTensorUnit X) ≪≫ (Functor.Monoidal.εIso F).symm).hom :=
  Iff.rfl

/-- Two tensor-compatible realizations of a monoidal functor are related by a
2-arrow inducing their given comparison. -/
theorem existsUnique_hom_of_rightExactTensor_spec
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [Groupoids.Hom.Affine (diagonal.{u + 1, u, u + 1} X)]
    {U : Over S} [IsAffine U.left]
    (F : QCoh X ⥤ ModuleCat.{u} Γ(U.left, ⊤)) [F.Monoidal]
    {f f' : GroupoidsOver.slice U ⟶ X}
    (t : F ≅ tensorPullback f) (t' : F ≅ tensorPullback f')
    (ht : IsTensorPullbackIso F t) (ht' : IsTensorPullbackIso F t') :
    ∃ α : f ⟶ f', t ≪≫ tensorPullbackIso α = t' :=
  sorry

/-- A right exact symmetric tensor functor on quasi-coherent modules of a
Noetherian algebraic stack with affine diagonal, preserving all small direct sums,
is induced by an essentially unique absolute morphism from the affine test scheme. -/
theorem existsUnique_hom_of_rightExactTensor
    {X : GroupoidsOver (Spec (.of (ULift.{u} ℤ)))} [AlgebraicStack X]
    [AlgebraicStack.IsNoetherian X]
    [Groupoids.Hom.Affine (diagonal.{u + 1, u, u + 1} X)]
    {U : Over (Spec (.of (ULift.{u} ℤ)))} [IsAffine U.left]
    (F : QCoh X ⥤ ModuleCat.{u} Γ(U.left, ⊤)) [F.Braided]
    [PreservesFiniteColimits F]
    [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F] :
    ∃ (f : GroupoidsOver.slice U ⟶ X) (t : F ≅ tensorPullback f),
      IsTensorPullbackIso F t ∧
        ∀ (f' : GroupoidsOver.slice U ⟶ X) (t' : F ≅ tensorPullback f'),
          IsTensorPullbackIso F t' →
            ∃ α : f ⟶ f', t ≪≫ tensorPullbackIso α = t' :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
