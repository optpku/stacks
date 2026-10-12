/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Sheafification
import Lean.Util.CollectAxioms

/-! # Canonical elimination of invertible denominators

The inverse is tied to the actual denominator-one map. Its localization
certificate is proved from invertibility of the displayed scalars; there is
no new existence or choice of an unrelated comparison map.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PullbackFactory

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.UnitDenominators

section Algebra

variable {R : Type u} [CommRing R] (D : Submonoid R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (hD : ∀ d : D, IsUnit (d : R))

include hD in
/-- When the actual denominators are units, the identity already has the localization property. -/
theorem identity_isLocalized : IsLocalizedModule D (LinearMap.id : M →ₗ[R] M) where
  map_units d := (hD d).map (algebraMap R (Module.End R M))
  surj m := ⟨(m, 1), by simp⟩
  exists_of_eq h := ⟨1, by simpa using h⟩

/-- The specified localization map contracts to the original module. -/
def collapse : LocalizedModule D M ≃ₗ[R] M := by
  -- Local instance justification (proof-local temporary data): Since every supplied denominator is a unit, the fixed identity map on M has the stated localization property and its canonical comparison is invertible.
  letI := identity_isLocalized D M hD
  exact IsLocalizedModule.iso D (LinearMap.id : M →ₗ[R] M)

theorem collapse_mk_one (m : M) : collapse D M hD (LocalizedModule.mk m 1) = m := by
  -- Local instance justification (proof-local temporary data): Since every supplied denominator is a unit, the fixed identity map on M has the stated localization property and its canonical comparison is invertible.
  letI := identity_isLocalized D M hD
  exact IsLocalizedModule.iso_mk_one D (LinearMap.id : M →ₗ[R] M) m

/-- The inverse is exactly the denominator-one constructor. -/
theorem collapse_symm (m : M) : (collapse D M hD).symm m = LocalizedModule.mk m 1 := by
  apply (collapse D M hD).injective
  rw [LinearEquiv.apply_symm_apply, collapse_mk_one]

/-- On a genuine fraction, evaluation clears precisely its displayed denominator. -/
theorem collapse_clears (m : M) (d : D) :
    (d : R) • collapse D M hD (LocalizedModule.mk m d) = m := by
  rw [← map_smul]
  have hc : (d : R) • (LocalizedModule.mk m d : LocalizedModule D M) =
      LocalizedModule.mk m 1 := by
    rw [LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_cancel d m
  rw [hc, collapse_mk_one]

end Algebra

section Space

variable {S : Scheme.{u}} (X : AlgebraicSpace S) (F : X.Modules)

abbrev Original := (Modules.liftModule F).val.presheaf
abbrev Fractions := (meromorphicSectionPresheaf X F).presheaf

/-- The actual numerator map into the meromorphic presheaf. -/
def numerator : Original X F ⟶ Fractions X F where
  app U := AddCommGrpCat.ofHom
    (LocalizedModule.mkLinearMap ((regularStructureSections X).obj U)
      ((Modules.liftModule F).val.obj U)).toAddMonoidHom
  naturality U V i := by
    ext m
    change LocalizedModule.mk (M := (Modules.liftModule F).val.obj V)
        ((Modules.liftModule F).val.map i m) 1 =
      meromorphicSectionRestrict X F i (LocalizedModule.mk m 1)
    change LocalizedModule.mk (M := (Modules.liftModule F).val.obj V)
        ((Modules.liftModule F).val.map i m) 1 =
      LocalizedModule.mk (M := (Modules.liftModule F).val.obj V)
        ((Modules.liftModule F).val.map i m)
        ⟨((commStructureSheafLift X).obj.map i).hom 1, _⟩
    congr 1
    apply Subtype.ext
    exact (map_one ((commStructureSheafLift X).obj.map i).hom).symm

theorem numerator_apply (U : (smallEtaleSite X)ᵒᵖ)
    (m : (Modules.liftModule F).val.obj U) :
    (numerator X F).app U m = LocalizedModule.mk m 1 := rfl

variable (hD : ∀ (U : (smallEtaleSite X)ᵒᵖ)
    (d : (regularStructureSections X).obj U),
      IsUnit (d : (commStructureSheafLift X).obj.obj U))

/-- Each component inverse is the certified contraction of actual fractions. -/
def numeratorAppIso (U : (smallEtaleSite X)ᵒᵖ) :
    (Original X F).obj U ≅ (Fractions X F).obj U :=
  (collapse ((regularStructureSections X).obj U)
    ((Modules.liftModule F).val.obj U) (hD U)).symm.toAddEquiv.toAddCommGrpIso

theorem numeratorAppIso_hom (U : (smallEtaleSite X)ᵒᵖ) :
    (numeratorAppIso X F hD U).hom = (numerator X F).app U := by
  ext m
  exact collapse_symm ((regularStructureSections X).obj U)
    ((Modules.liftModule F).val.obj U) (hD U) m

/-- The numerator map is an isomorphism because its actual components have proved inverses. -/
def numeratorIso : Original X F ≅ Fractions X F :=
  NatIso.ofComponents (numeratorAppIso X F hD) (by
    intro U V i
    simp only [numeratorAppIso_hom]
    exact (numerator X F).naturality i)

include hD in
theorem fractions_isSheaf : Presheaf.IsSheaf (smallEtaleTopology X) (Fractions X F) :=
  (Presheaf.isSheaf_of_iso_iff (J := smallEtaleTopology X) (numeratorIso X F hD)).mp
    (Modules.liftModule F).isSheaf

/-- Canonical sheaf-level elimination: invert the certified sheafification unit, then contract. -/
def sheafEvaluation : (meromorphicSectionSheaf X F).val.presheaf ⟶ Original X F := by
  -- Local instance justification (defeq pin): Use the named additive sheafification adjunction at X to identify the specified localization sheaf and its unit.
  letI := Sheafification.additiveCertificate X
  exact (CategoryTheory.isoSheafify (smallEtaleTopology X)
    (fractions_isSheaf X F hD)).inv ≫ (numeratorIso X F hD).inv

/-- On a sheafified fraction the map is exactly localization contraction. -/
theorem sheafEvaluation_fraction (U : (smallEtaleSite X)ᵒᵖ)
    (q : (Fractions X F).obj U) :
    (sheafEvaluation X F hD).app U ((Sheafification.unit X F).app U q) =
      collapse ((regularStructureSections X).obj U)
        ((Modules.liftModule F).val.obj U) (hD U) q := by
  -- Local instance justification (defeq pin): Use the named additive sheafification adjunction at X to identify the specified localization sheaf and its unit.
  letI := Sheafification.additiveCertificate X
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (CategoryTheory.isoSheafify (smallEtaleTopology X)
      (fractions_isSheaf X F hD)).hom_inv_id U) q
  exact congrArg ((numeratorIso X F hD).inv.app U) h

/-- Specialized computation rule avoids expanding the localization tower downstream. -/
theorem sheafEvaluation_numerator (U : (smallEtaleSite X)ᵒᵖ)
    (m : (Modules.liftModule F).val.obj U) :
    (sheafEvaluation X F hD).app U ((Sheafification.unit X F).app U
      (LocalizedModule.mk m 1)) = m :=
  (sheafEvaluation_fraction X F hD U (LocalizedModule.mk m 1)).trans
    (collapse_mk_one ((regularStructureSections X).obj U)
      ((Modules.liftModule F).val.obj U) (hD U) m)

end Space

end AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.UnitDenominators

run_cmd do
  for n in [`AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.UnitDenominators.identity_isLocalized,
      `AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.UnitDenominators.collapse,
      `AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.UnitDenominators.collapse_symm,
      `AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.UnitDenominators.collapse_clears] do
    let axs ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms n)
    unless axs.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "UNCERTIFIED_UNIT_LOCALIZATION {n}: {axs}"
    Lean.logInfo m!"UNIT_LOCALIZATION_KERNEL_PASS|{n}|{axs}"
