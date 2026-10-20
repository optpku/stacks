/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap108.Lemma_108_4_9_ModulesGrothendieck
public import stacks_project.Chap108.Lemma_108_4_9_SliceHomSmall
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
  (R : Sheaf (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X) RingCat.{u})

/-- The actual local module-morphism type is small, by restriction to the certified slice basis. -/
theorem spaceLocalHomSmall (M N : SheafOfModules.{u} R)
    (U : AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X) :
    Small.{u} (M.over U ⟶ N.over U) := by
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : (spaceBasisInclusion X).Full := (fullyFaithfulInducedFunctor (spaceAffineInclusion X).obj).full
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : (spaceBasisInclusion X).Faithful :=
    (fullyFaithfulInducedFunctor (spaceAffineInclusion X).obj).faithful
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := spaceBasisCoverDense X
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := sliceModulesLocallySmall (spaceBasisInclusion X)
    (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X) R U
  infer_instance

-- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
local instance certifiedLocalHomSmall (M N : SheafOfModules.{u} R)
    (U : AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X) :
    Small.{u} (M.over U ⟶ N.over U) := spaceLocalHomSmall X R M N U

/-- A certified small carrier of actual local sheaf morphisms, not maps between section modules. -/
noncomputable def smallLocalHom (M N : SheafOfModules.{u} R)
    (U : (AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X)ᵒᵖ) : Type u :=
  Shrink.{u} (M.over U.unop ⟶ N.over U.unop)

/-- The carrier equivalence is backed by the proved size certificate. -/
noncomputable def smallLocalHomEquiv (M N : SheafOfModules.{u} R)
    (U : (AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X)ᵒᵖ) :
    (M.over U.unop ⟶ N.over U.unop) ≃ smallLocalHom X R M N U :=
  equivShrink _

/-- Restriction transports the real slice morphism, exactly as in the canonical LocalHom owner. -/
noncomputable def smallLocalHomRestrict (M N : SheafOfModules.{u} R)
    {U V : (AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X)ᵒᵖ} (i : U ⟶ V)
    (f : smallLocalHom X R M N U) : smallLocalHom X R M N V :=
  smallLocalHomEquiv X R M N V
    ((SheafOfModules.overFunctorMap R i.unop).inv.app M ≫
      (SheafOfModules.overMap R i.unop).map ((smallLocalHomEquiv X R M N U).symm f) ≫
        (SheafOfModules.overFunctorMap R i.unop).hom.app N)

/-- Decoding the restricted carrier gives the actual canonical restriction formula. -/
theorem smallLocalHomRestrict_decode (M N : SheafOfModules.{u} R)
    {U V : (AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X)ᵒᵖ} (i : U ⟶ V)
    (f : smallLocalHom X R M N U) :
    (smallLocalHomEquiv X R M N V).symm (smallLocalHomRestrict X R M N i f) =
      (SheafOfModules.overFunctorMap R i.unop).inv.app M ≫
        (SheafOfModules.overMap R i.unop).map ((smallLocalHomEquiv X R M N U).symm f) ≫
          (SheafOfModules.overFunctorMap R i.unop).hom.app N :=
  (smallLocalHomEquiv X R M N V).symm_apply_apply _

private theorem transport_identity {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (A : C) {B : D} (e : F.obj A ≅ B) :
    e.inv ≫ F.map (𝟙 A) ≫ e.hom = 𝟙 B := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp, e.inv_hom_id]

/-- A genuine local identity morphism remains the identity after restriction. -/
theorem smallLocalHomRestrict_identity (M : SheafOfModules.{u} R)
    {U V : (AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    smallLocalHomRestrict X R M M i (smallLocalHomEquiv X R M M U (𝟙 _)) =
      smallLocalHomEquiv X R M M V (𝟙 _) := by
  apply (smallLocalHomEquiv X R M M V).symm.injective
  rw [smallLocalHomRestrict_decode, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact transport_identity (SheafOfModules.overMap R i.unop) (M.over U.unop)
    ((SheafOfModules.overFunctorMap R i.unop).app M)

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site
