/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Adjunction.Additive
public import stacks_project.Chap46.Lemma_46_4_10
public import stacks_project.Chap46.Lemma_46_7_3

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace SheafOfModules.AffineAdeq

/-- The ambient category of module sheaves on the big `τ`-site of `Spec A` is
abelian at the universe used by affine adequate sheaves. -/
noncomputable instance ambientAbelian (τ : StandardTopology) (A : CommRingCat.{u}) :
    Abelian (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A)))) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

/-- The category of adequate module sheaves on the big `τ`-site of `Spec A` has
finite products, transported through affine evaluation. -/
instance instHasFiniteProducts (τ : StandardTopology) (A : CommRingCat.{u}) :
    HasFiniteProducts (AffineAdeq τ A) :=
  ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence
    (SheafOfModules.affineEvaluationAdequate τ A)⟩

/-- The category of adequate module sheaves on the big `τ`-site of `Spec A` is
abelian, via the affine-evaluation equivalence. -/
noncomputable instance instAbelian (τ : StandardTopology) (A : CommRingCat.{u}) :
    Abelian (AffineAdeq τ A) :=
  abelianOfEquivalence (SheafOfModules.affineEvaluationAdequate τ A)

/-- The right adjoint to the inclusion of affine adequate module sheaves is additive. -/
instance coreflectorAdditive (τ : StandardTopology) (A : CommRingCat.{u}) :
    (inclusion τ A).rightAdjoint.Additive :=
  (Adjunction.ofIsLeftAdjoint (inclusion τ A)).right_adjoint_additive

end SheafOfModules.AffineAdeq
