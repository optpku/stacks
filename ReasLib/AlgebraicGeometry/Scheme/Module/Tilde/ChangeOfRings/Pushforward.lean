/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.ChangeOfRings.GlobalSections
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushforward in affine change of rings

Pushforward along an affine spectrum map is compared with restriction of scalars.  The final
comparison reuses mathlib's canonical tilde equivalence; its current implementation packages
the inverse of the canonical counit with `asIso`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.tilde.ChangeOfRings.Pushforward

/-- Pushforward of affine tilde sheaves, valued in quasicoherent modules. -/
@[stacks 01I9 "pushforward tilde as a quasicoherent functor"]
noncomputable def functor
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    ModuleCat S ⥤ Scheme.QCoh (Spec R) :=
  (tildeEquiv (R := S)).functor ⋙ Scheme.QCoh.pushforward (Spec.map φ)

/-- Forgetting quasicoherence after affine pushforward recovers pushforward of tilde sheaves. -/
@[stacks 01I9 "pushforward tilde inclusion comparison"]
noncomputable def compInclusionIso
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    functor φ ⋙ Scheme.QCoh.inclusion (Spec R) ≅
      tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tildeEquiv (R := S)).functor
      (Scheme.QCoh.pushforward.inclusionIso (Spec.map φ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Iso.refl (tilde.functor S))
      (Scheme.Modules.pushforward (Spec.map φ))

/-- The quasicoherent lift of pushforward has the expected module of global sections. -/
@[stacks 01I9 "global sections of quasicoherent affine pushforward"]
noncomputable def sectionsIso
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    functor φ ⋙ (tildeEquiv (R := R)).inverse ≅
      ModuleCat.restrictScalars φ.hom :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (compInclusionIso φ)
      (moduleSpecΓFunctor (R := R)) ≪≫
    GlobalSections.pushforwardIso φ

/-- Pushforward along `Spec.map φ` canonically commutes with affine tilde sheafification and
restriction of scalars. -/
@[stacks 01I9 "pushforward"]
noncomputable def iso
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ) ≅
      ModuleCat.restrictScalars φ.hom ⋙ tilde.functor R :=
  (compInclusionIso φ).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.rightUnitor (functor φ)).symm ≪≫
        Functor.isoWhiskerLeft (functor φ)
          (tildeEquiv (R := R)).counitIso.symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (sectionsIso φ)
          (tildeEquiv (R := R)).functor)
      (Scheme.QCoh.inclusion (Spec R)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ModuleCat.restrictScalars φ.hom)
      (Iso.refl (tilde.functor R))

/-- The hom component of `iso` is compatible with the affine tilde counit. -/
@[reassoc (attr := simp), stacks 01I9 "pushforward change-of-rings hom compatibility"]
theorem fromTildeΓ_hom_app
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat S) :
    Scheme.Modules.fromTildeΓ
        ((tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ)).obj M) ≫
      (iso φ).hom.app M =
        tilde.map ((GlobalSections.pushforwardIso φ).hom.app M) := sorry

/-- The inverse component of `iso` is compatible with the affine tilde counit. -/
@[reassoc (attr := simp), stacks 01I9 "pushforward change-of-rings inverse compatibility"]
theorem inv_app_fromTildeΓ
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat S) :
    tilde.map ((GlobalSections.pushforwardIso φ).hom.app M) ≫
      (iso φ).inv.app M =
        Scheme.Modules.fromTildeΓ
          ((tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ)).obj M) := sorry

end AlgebraicGeometry.tilde.ChangeOfRings.Pushforward

section

variable (R : CommRingCat.{u})

end
