/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.TensorExtension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafificationCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.Ring.Sheaf

/-! # Specified tensor/sheafification scalar-extension adjunction

Scalar extension is defined by tensoring the given module presheaf, then
sheafifying. Its adjunction is assembled from the actual tensor Hom maps
and the actual sheafification adjunction, not by selecting a left adjoint.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Presheaf

noncomputable section

universe u v w z

namespace AlgebraicGeometry.AlgebraicSpace.PullbackFactory.SheafTensorExtension

open AlgebraicGeometry.AlgebraicSpace.PullbackFactory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {R R' : Sheaf J CommRingCat.{w}} (α : R ⟶ R')

abbrev sourceRing := CategoryTheory.Sheaf.ringSheafOfComm R
abbrev targetRing := CategoryTheory.Sheaf.ringSheafOfComm R'
abbrev ringMap := CategoryTheory.Sheaf.ringSheafOfCommMap α

theorem identityLocallyInjective : Presheaf.IsLocallyInjective J
    (𝟙 (targetRing (R' := R')).obj) :=
  Presheaf.isLocallyInjective_of_injective J (𝟙 (targetRing (R' := R')).obj)
    (fun _ x y h => by simpa using h)

theorem identityLocallySurjective : Presheaf.IsLocallySurjective J
    (𝟙 (targetRing (R' := R')).obj) :=
  Presheaf.isLocallySurjective_of_surjective J (𝟙 (targetRing (R' := R')).obj)
    (fun _ x => ⟨x, by simp⟩)

variable [HasWeakSheafify J AddCommGrpCat.{max w z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max w z}]

/-- The given module's actual tensor presheaf, followed by sheafification. -/
def sheafifyTarget : PresheafOfModules.{max w z} (targetRing (R' := R')).obj ⥤
    SheafOfModules.{max w z} (targetRing (R' := R')) := by
  -- Local instance justification (defeq pin): Supply local injectivity of the specified identity ring map used by this tensor sheafification adjunction.
  letI := identityLocallyInjective (R' := R')
  -- Local instance justification (defeq pin): Supply local surjectivity of the same identity ring map; no alternative coefficient map is selected.
  letI := identityLocallySurjective (R' := R')
  exact PresheafOfModules.sheafification (J := J) (R := targetRing (R' := R'))
    (𝟙 (targetRing (R' := R')).obj)

def extension : SheafOfModules.{max w z} (sourceRing (R := R)) ⥤
    SheafOfModules.{max w z} (targetRing (R' := R')) :=
  SheafOfModules.forget _ ⋙ PresheafTensorExtension.functor α.hom ⋙
    sheafifyTarget (R' := R')

/-- The right functor is the existing, explicit restriction of scalars. -/
abbrev restriction := SheafOfModules.restrictScalars.{max w z} (ringMap α)

/-- Both Hom functions are prescribed: sheafification unit, tensor Hom maps,
then the fully faithful forgetful correspondence for module sheaves. -/
def homEquiv (M : SheafOfModules.{max w z} (sourceRing (R := R)))
    (N : SheafOfModules.{max w z} (targetRing (R' := R'))) :
    ((extension α).obj M ⟶ N) ≃ (M ⟶ (restriction α).obj N) :=
  -- Local instance justification (defeq pin): Supply local injectivity of the specified identity ring map used by this tensor sheafification adjunction.
  letI := identityLocallyInjective (R' := R')
  -- Local instance justification (defeq pin): Supply local surjectivity of the same identity ring map; no alternative coefficient map is selected.
  letI := identityLocallySurjective (R' := R')
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (targetRing (R' := R')).obj)).homEquiv _ _).trans
    ((PresheafTensorExtension.adjunction α.hom).homEquiv _ _ |>.trans
      ((SheafOfModules.fullyFaithfulForget _).homEquiv
        (X := M) (Y := (restriction α).obj N)).symm)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality is inherited from the two specified adjunctions and the forgetful functor. -/
def adjunction : extension α ⊣ restriction α :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv α
      homEquiv_naturality_left_symm := by
        intro M N P f g
        change ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (targetRing (R' := R')).obj)).homEquiv _ _).symm
          (((PresheafTensorExtension.adjunction α.hom).homEquiv _ _).symm (f.val ≫ g.val)) = _
        rw [Adjunction.homEquiv_naturality_left_symm,
          Adjunction.homEquiv_naturality_left_symm]
        rfl
      homEquiv_naturality_right := by
        intro M N P f g
        apply SheafOfModules.hom_ext
        change (PresheafTensorExtension.adjunction α.hom).homEquiv _ _
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (targetRing (R' := R')).obj)).homEquiv _ _ (f ≫ g)) = _
        rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
        rfl }

/-- The right-adjoint certificate now contains the explicit tensor/sheafification witness. -/
theorem restriction_isRightAdjoint : (restriction.{u, v, w, z} α).IsRightAdjoint :=
  (adjunction.{u, v, w, z} α).isRightAdjoint

/-- The actual tensor unit at presheaf level is the transpose of the identity. -/
def tensorUnit (M : SheafOfModules.{max w z} (sourceRing (R := R))) :
    M.val ⟶ (PresheafOfModules.restrictScalars
      (PresheafOfModules.presheafStructureMap α.hom)).obj
        (PresheafTensorExtension.presheaf α.hom M.val) :=
  (PresheafTensorExtension.adjunction α.hom).unit.app M.val

omit [HasWeakSheafify J AddCommGrpCat.{max w z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w z}] in
/-- On each section the prescribed tensor unit is exactly `1 tensor m`. -/
theorem tensorUnit_apply (M : SheafOfModules.{max w z} (sourceRing (R := R)))
    (U : Cᵒᵖ) (m : M.val.obj U) :
    -- Local instance justification (defeq pin): The displayed pure tensor uses exactly the scalar action of the supplied sheaf coefficient map α at U.
    letI := (α.hom.app U).hom.toAlgebra
    (tensorUnit α M).app U m = (1 : R'.obj.obj U) ⊗ₜ[R.obj.obj U] m := by
  rfl

/-- The sheaf unit is the tensor unit followed by the actual sheafification unit. -/
def explicitUnit (M : SheafOfModules.{max w z} (sourceRing (R := R))) :
    M ⟶ (restriction α).obj ((extension α).obj M) where
  val := tensorUnit α M ≫
    (PresheafOfModules.restrictScalars
      (PresheafOfModules.presheafStructureMap α.hom)).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (targetRing (R' := R')).obj)).unit.app
            (PresheafTensorExtension.presheaf α.hom M.val))

theorem unit_eq_explicitUnit (M : SheafOfModules.{max w z} (sourceRing (R := R))) :
    (adjunction α).unit.app M = explicitUnit α M := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  rfl

section Certified

variable {D : Type (u + 1)} [Category.{u} D] (K : GrothendieckTopology D)
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A B : Sheaf K CommRingCat.{u}} (β : A ⟶ B)

/-- The concrete extension in coefficient universe `u+1` explicitly binds the
proved plus-construction certificates on a site of this size. -/
def certifiedExtension : SheafOfModules.{u + 1} (Sheaf.ringSheafOfComm A) ⥤
    SheafOfModules.{u + 1} (Sheaf.ringSheafOfComm B) := by
  -- Local instance justification (defeq pin): Use the named coefficient sheafification adjunction on K at universe u+1 for this explicit extension functor.
  letI : HasWeakSheafify K AddCommGrpCat.{u + 1} :=
    (CoefficientSheafification.additive K).isRightAdjoint
  -- Local instance justification (defeq pin): The chosen coefficient sheafification on K inverts precisely locally bijective additive maps, as its named law states.
  letI := CoefficientSheafification.additiveW K
  exact extension.{u + 1, u, u, u + 1} β

/-- This is a fully specified adjunction, with sheafification existence proved
at the original site size. No assumed scalar-extension adjoint is an input. -/
def certifiedAdjunction : certifiedExtension K β ⊣
    SheafOfModules.restrictScalars.{u + 1} (Sheaf.ringSheafOfCommMap β) := by
  -- Local instance justification (defeq pin): Use the named coefficient sheafification adjunction on K at universe u+1 for this explicit extension functor.
  letI : HasWeakSheafify K AddCommGrpCat.{u + 1} :=
    (CoefficientSheafification.additive K).isRightAdjoint
  -- Local instance justification (defeq pin): The chosen coefficient sheafification on K inverts precisely locally bijective additive maps, as its named law states.
  letI := CoefficientSheafification.additiveW K
  exact adjunction.{u + 1, u, u, u + 1} β

end Certified

section LiftedCertified

variable {D : Type (u + 1)} [Category.{u} D] (K : GrothendieckTopology D)
    [K.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    {A B : Sheaf K CommRingCat.{u + 1}} (β : A ⟶ B)

/-- The same explicit functor for the universe-lifted coefficients already
used by the algebraic-space meromorphic-module pipeline. -/
def certifiedLiftedExtension : SheafOfModules.{u + 1} (Sheaf.ringSheafOfComm A) ⥤
    SheafOfModules.{u + 1} (Sheaf.ringSheafOfComm B) := by
  -- Local instance justification (defeq pin): Use the named coefficient sheafification adjunction on K at universe u+1 for this explicit extension functor.
  letI : HasWeakSheafify K AddCommGrpCat.{u + 1} :=
    (CoefficientSheafification.additive K).isRightAdjoint
  -- Local instance justification (defeq pin): The chosen coefficient sheafification on K inverts precisely locally bijective additive maps, as its named law states.
  letI := CoefficientSheafification.additiveW K
  exact extension.{u + 1, u, u + 1, u + 1} β

def certifiedLiftedAdjunction : certifiedLiftedExtension K β ⊣
    SheafOfModules.restrictScalars.{u + 1} (Sheaf.ringSheafOfCommMap β) := by
  -- Local instance justification (defeq pin): Use the named coefficient sheafification adjunction on K at universe u+1 for this explicit extension functor.
  letI : HasWeakSheafify K AddCommGrpCat.{u + 1} :=
    (CoefficientSheafification.additive K).isRightAdjoint
  -- Local instance justification (defeq pin): The chosen coefficient sheafification on K inverts precisely locally bijective additive maps, as its named law states.
  letI := CoefficientSheafification.additiveW K
  exact adjunction.{u + 1, u, u + 1, u + 1} β

end LiftedCertified

end AlgebraicGeometry.AlgebraicSpace.PullbackFactory.SheafTensorExtension
