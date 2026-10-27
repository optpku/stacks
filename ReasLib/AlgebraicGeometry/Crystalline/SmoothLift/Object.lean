/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Crystalline.SmoothLift.DividedPowers
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Coefficients

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
universe u
namespace AlgebraicGeometry.Scheme.Crystalline.SmoothLift

variable {p : ℕ} [Fact p.Prime]
variable {A : Type u} [CommRing A] {IA : Ideal A} (γA : DividedPowers IA)
variable {Y : Scheme.{u}} (yToS : Y ⟶ Spec (.of A)) [Smooth yToS]
variable (I : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable (hI : Scheme.Crystalline.Affine.idealCompatible IA I) (hγ : Scheme.Crystalline.Affine.dividedPowersCompatible IA γA I γS)
variable (hpnil : IsNilpotent (p : A))

include γA hI hpnil in
/-- In a p-nilpotent PD ring every element of its PD ideal is nilpotent.
After smooth base change this makes the actual closed-fibre inclusion a
thickening. Matching the affine ideal and p-nilpotence are both retained. -/
theorem inclusion_thickening : IsThickening (smoothLift_inclusion yToS I) := sorry

include hpnil in
/-- The kernel ideal of the actual closed-fibre map, with the uniquely
extended divided powers, defines a genuine thickening. -/
theorem ideal_thickening :
    IsDividedPowerThickening Y (smoothLift_inclusion yToS I).ker
      (smoothLiftDividedPowers γA yToS I hI)
      (smoothLiftDividedPowers_compatible γA yToS I hI) := sorry

/-- The actual smooth-lift crystalline object. Its geometric fields are
the closed-fibre square; both thickening obligations consume p-nilpotence. -/
noncomputable def object :
    CrystallineObject (Spec (.of A)) I γS hc
      (smoothLift yToS I) (smoothLift_x₀ yToS I) where
  source := Over.mk (𝟙 (smoothLift yToS I))
  thickening := Y
  thickeningToBase := yToS
  inclusion := smoothLift_inclusion yToS I
  ideal := (smoothLift_inclusion yToS I).ker
  gamma := smoothLiftDividedPowers γA yToS I hI
  thickening_compatible := smoothLiftDividedPowers_compatible γA yToS I hI
  isThickening := ideal_thickening γA yToS I hI hpnil
  inclusion_isThickening := inclusion_thickening γA yToS I hI hpnil
  ideal_eq_ker := rfl
  source_comm := by
    change pullback.fst yToS I.subschemeι ≫ yToS =
      𝟙 _ ≫ pullback.snd yToS I.subschemeι ≫ I.subschemeι
    rw [Category.id_comp]
    exact pullback.condition

include hγ in
/-- The extended PD structure agrees with the base structure because hγ
identifies the base ring's divided powers with the sheaf-level data. -/
theorem object_baseCompatible :
    CrystallineBaseCompatible I γS hc (smoothLift_x₀ yToS I)
      (object γA yToS I γS hc hI hpnil) := sorry

/-- The identity on the closed fibre is open, so the genuine object lies
in the small crystalline site. -/
noncomputable def smallObject :
    smallCrystallineSite (Spec (.of A)) I γS hc
      (smoothLift yToS I) (smoothLift_x₀ yToS I) where
  obj := ⟨object γA yToS I γS hc hI hpnil,
    object_baseCompatible γA yToS I γS hc hI hγ hpnil⟩
  property := by
    change IsOpenImmersion (𝟙 (smoothLift yToS I))
    infer_instance

/-- The smooth-lift object retains Y as its thickening, without a chosen
scheme equivalence or a substituted affine spectrum of global functions. -/
theorem smallObject_thickening :
    (smallObject γA yToS I γS hc hI hγ hpnil).obj.1.thickening = Y := rfl

/-- The coefficient sheaf on Y is the actual crystal's value at the
smooth-lift object, preserving all local sections. -/
noncomputable def coefficient
    (F : CrystallineModuleSheaf.CrisModuleSheaf (Spec (.of A)) I γS hc
      (smoothLift yToS I) (smoothLift_x₀ yToS I)) : Y.Modules :=
  F.obj (smallObject γA yToS I γS hc hI hγ hpnil)


end AlgebraicGeometry.Scheme.Crystalline.SmoothLift
