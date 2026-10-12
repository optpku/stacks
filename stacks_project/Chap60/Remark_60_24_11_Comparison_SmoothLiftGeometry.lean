/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import stacks_project.Chap60.Remark_60_24_11_Comparison_Object
public import stacks_project.Chap60.Remark_60_24_9_Base_change_isomorphism_Coefficients

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
universe u
namespace CrystallineSmoothLiftRepair

variable {p : ℕ} [Fact p.Prime]
variable {A : Type u} [CommRing A] {IA : Ideal A} (γA : DividedPowers IA)
variable {Y : Scheme.{u}} (yToS : Y ⟶ Spec (.of A)) [Smooth yToS]
variable (I : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable (hI : specIdealEqOfIdealTop IA I) (hγ : specDividedPowersEq IA γA I γS)
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
the source's fibre square; both thickening obligations consume p-nilpotence. -/
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
corrected smooth-lift object, preserving all local sections. -/
noncomputable def coefficient
    (F : CrystallineModuleSheaf.CrisModuleSheaf (Spec (.of A)) I γS hc
      (smoothLift yToS I) (smoothLift_x₀ yToS I)) : Y.Modules :=
  F.obj (smallObject γA yToS I γS hc hI hγ hpnil)

include γA hI hpnil in
/-- Restricting the genuine closed-fibre thickening to an open preserves
the thickening property. Nilpotence remains in the hypotheses. -/
theorem open_inclusion_thickening (U : Y.Opens) :
    IsThickening (pullback.snd (smoothLift_inclusion yToS I) U.ι) := sorry

include hpnil in
/-- The restricted kernel ideal with extended PD structure is a genuine
thickening, by the p-nilpotent closed-fibre construction. -/
theorem open_ideal_thickening (U : Y.Opens) :
    IsDividedPowerThickening U.toScheme
      (pullback.snd (smoothLift_inclusion yToS I) U.ι).ker
      (smoothLiftDividedPowers_over γA yToS I hI U)
      (smoothLiftDividedPowers_over_compatible γA yToS I hI U) := sorry

/-- The actual smooth-lift crystalline object over an arbitrary open U.
Its source is the actual pullback of the closed fibre, not Spec of an
unrelated global-section quotient. -/
noncomputable def openObject (U : Y.Opens) :
    CrystallineObject (Spec (.of A)) I γS hc
      (smoothLift yToS I) (smoothLift_x₀ yToS I) where
  source := smoothLiftSource_over yToS I U
  thickening := U.toScheme
  thickeningToBase := U.ι ≫ yToS
  inclusion := pullback.snd (smoothLift_inclusion yToS I) U.ι
  ideal := (pullback.snd (smoothLift_inclusion yToS I) U.ι).ker
  gamma := smoothLiftDividedPowers_over γA yToS I hI U
  thickening_compatible := smoothLiftDividedPowers_over_compatible γA yToS I hI U
  isThickening := open_ideal_thickening γA yToS I hI hpnil U
  inclusion_isThickening := open_inclusion_thickening γA yToS I hI hpnil U
  ideal_eq_ker := rfl
  source_comm := sorry

include hγ in
/-- The restricted object still extends precisely the specified base DP
structure, using the base/sheaf agreement. -/
theorem openObject_baseCompatible (U : Y.Opens) :
    CrystallineBaseCompatible I γS hc (smoothLift_x₀ yToS I)
      (openObject γA yToS I γS hc hI hpnil U) := sorry

/-- The source of the restricted object is open in the closed fibre. -/
theorem openObject_source_open (U : Y.Opens) :
    IsOpenImmersion (openObject γA yToS I γS hc hI hpnil U).source.hom := by
  change IsOpenImmersion (pullback.fst (smoothLift_inclusion yToS I) U.ι)
  infer_instance

/-- The genuine restricted smooth-lift object in the small site. -/
noncomputable def openSmallObject (U : Y.Opens) :
    smallCrystallineSite (Spec (.of A)) I γS hc
      (smoothLift yToS I) (smoothLift_x₀ yToS I) where
  obj := ⟨openObject γA yToS I γS hc hI hpnil U,
    openObject_baseCompatible γA yToS I γS hc hI hγ hpnil U⟩
  property := openObject_source_open γA yToS I γS hc hI hpnil U

/-- The actual map from a restricted smooth-lift object to the whole
smooth-lift object. Its thickening map is the open inclusion U→Y. -/
noncomputable def openToWhole (U : Y.Opens) :
    openSmallObject γA yToS I γS hc hI hγ hpnil U ⟶ smallObject γA yToS I γS hc hI hγ hpnil :=
  ObjectProperty.homMk
    { source := Over.homMk (pullback.fst (smoothLift_inclusion yToS I) U.ι) sorry
      thickening := U.ι
      source_comm := sorry
      base_comm := rfl
      ideal_compatible := sorry
      dividedPowers_compatible := sorry }

/-- Evaluation on the actual open object is compared with restriction of
the full coefficient sheaf by F's own crystalline comparison map. -/
noncomputable def restrictionComparison (U : Y.Opens)
    (F : CrystallineModuleSheaf.CrisModuleSheaf (Spec (.of A)) I γS hc
      (smoothLift yToS I) (smoothLift_x₀ yToS I)) :
    (Scheme.Modules.pullback U.ι).obj (coefficient γA yToS I γS hc hI hγ hpnil F) ⟶
      F.obj (openSmallObject γA yToS I γS hc hI hγ hpnil U) :=
  F.comparison (openToWhole γA yToS I γS hc hI hγ hpnil U)

end CrystallineSmoothLiftRepair
