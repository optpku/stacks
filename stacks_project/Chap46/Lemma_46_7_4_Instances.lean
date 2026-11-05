/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Derived
public import stacks_project.Chap46.Lemma_46_4_10
public import stacks_project.Chap46.Lemma_46_7_3

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

/- The ambient category of module sheaves on the big `τ`-site of `Spec A` is abelian. -/
#check (SheafOfModules.AffineAdeq.ambientAbelian :
  ∀ (τ : StandardTopology) (A : CommRingCat.{u}),
    Abelian (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A)))))

/- The category of affine adequate module sheaves has finite products. -/
#check (SheafOfModules.AffineAdeq.affineAdeq_hasFiniteProducts :
  ∀ (τ : StandardTopology) (A : CommRingCat.{u}),
    HasFiniteProducts (SheafOfModules.AffineAdeq τ A))

/- The category of affine adequate module sheaves is abelian. -/
#check (SheafOfModules.AffineAdeq.affineAdeqAbelian :
  ∀ (τ : StandardTopology) (A : CommRingCat.{u}),
    Abelian (SheafOfModules.AffineAdeq τ A))

/- The right adjoint to the inclusion of affine adequate module sheaves is additive. -/
#check (SheafOfModules.AffineAdeq.coreflectorAdditive :
  ∀ (τ : StandardTopology) (A : CommRingCat.{u}),
    (SheafOfModules.AffineAdeq.inclusion τ A).rightAdjoint.Additive)
