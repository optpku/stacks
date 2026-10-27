/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Differentials
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.DividedPower.Canonical
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.SquareZeroExtension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.TrivSqZeroExt
public import ReasLib.RingTheory.DividedPowers.FirstOrder

/-!
# The divided-power first-order crystalline thickening

The square-zero extension by canonical divided-power relative differentials has two
distinguished sections: the constant section and the universal Taylor section. Its full
coordinate ideal carries the coordinate divided powers.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Crystalline
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace CrystallineObject.DividedPowerFirstOrderThickening

variable {S : Scheme.{u}} {I : S.IdealSheafData}
  {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
  {h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
  {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
  (T : smallCrystallineSite S I γ h_compatible X x₀)

/-- The defining ideal of a crystalline thickening is quasi-coherent. -/
theorem ideal_isQuasicoherent : T.obj.1.ideal.toModule.IsQuasicoherent := sorry

/-- The canonical divided-power relative differentials of a crystalline thickening. -/
abbrev differentials :=
  DividedPowerScheme.RelativeDifferentials.canonical
    { scheme := T.obj.1.thickening
      ideal := T.obj.1.ideal
      quasiCoherent := ideal_isQuasicoherent T
      dividedPowers := T.obj.1.gamma
      compatible := T.obj.1.thickening_compatible }
    S T.obj.1.thickeningToBase

/-- The square-zero ring of sections with divided-power differential coordinate. -/
def ring (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) : CommRingCat.{u} :=
  CommRingCat.of (TrivSqZeroExt (T.obj.1.thickening.presheaf.obj V)
    ((differentials T).module.val.obj V))

/-- Restrictions act separately on functions and divided-power differentials. -/
def map {U V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ} (ρ : U ⟶ V) :
    ring T U ⟶ ring T V := by
  refine CommRingCat.ofHom
    { toFun := fun z ↦ (T.obj.1.thickening.presheaf.map ρ z.1,
        (differentials T).module.val.map ρ z.2)
      map_zero' := ?_, map_one' := ?_, map_add' := ?_, map_mul' := ?_ }
  all_goals sorry

/-- The square-zero presheaf with the divided-power differential coordinate. -/
def presheaf : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ ⥤ CommRingCat.{u} := by
  refine { obj := ring T, map := map T, map_id := ?_, map_comp := ?_ }
  all_goals sorry

/-- The square-zero sheaf with the divided-power differential coordinate. -/
def sheaf : TopCat.Sheaf CommRingCat.{u} T.obj.1.thickening.toTopCat :=
  ⟨presheaf T, by sorry⟩

/-- The projection to the function coordinate on sections. -/
def projectionApp (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) :
    (sheaf T).obj.obj V ⟶ T.obj.1.thickening.presheaf.obj V :=
  CommRingCat.ofHom (TrivSqZeroExt.fstHom
    (T.obj.1.thickening.presheaf.obj V) (T.obj.1.thickening.presheaf.obj V)
    ((differentials T).module.val.obj V)).toRingHom

/-- The projection from the square-zero sheaf to the original structure sheaf. -/
def projection : sheaf T ⟶ T.obj.1.thickening.sheaf :=
  ObjectProperty.homMk { app := projectionApp T, naturality := by sorry }

/-- The projection of the split square-zero sheaf is locally surjective. -/
instance projection_isLocallySurjective :
    CategoryTheory.Sheaf.IsLocallySurjective (projection T) := sorry

/-- The differential-coordinate kernel squares to zero. -/
theorem projection_isSquareZero : KernelIdeal.IsSquareZero (projection T) := sorry

/-- The differential-coordinate kernel is a quasi-coherent module sheaf. -/
instance projection_kernel_isQuasicoherent :
    (Scheme.SquareZeroExtension.kernelModule (sheaf T) (projection T)
      (projection_isSquareZero T)).IsQuasicoherent := sorry

/-- The scheme with structure sheaf the split extension by divided-power differentials. -/
def scheme : Scheme.{u} :=
  Scheme.SquareZeroExtension.scheme (sheaf T) (projection T) (projection_isSquareZero T)

/-- The closed immersion defined by projection onto the function coordinate. -/
def schemeInclusion : T.obj.1.thickening ⟶ scheme T :=
  Scheme.SquareZeroExtension.ι (sheaf T) (projection T) (projection_isSquareZero T)

/-- The constant section on each open. -/
def zeroLiftApp (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) :
    T.obj.1.thickening.presheaf.obj V ⟶ (sheaf T).obj.obj V :=
  CommRingCat.ofHom (TrivSqZeroExt.inlHom (T.obj.1.thickening.presheaf.obj V)
    ((differentials T).module.val.obj V))

/-- The constant section of the square-zero projection. -/
def zeroLift : T.obj.1.thickening.sheaf ⟶ sheaf T :=
  ObjectProperty.homMk { app := zeroLiftApp T, naturality := by sorry }

/-- The Taylor section sends a function to itself together with its divided-power differential. -/
def differentialLiftApp (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ) :
    T.obj.1.thickening.presheaf.obj V ⟶ (sheaf T).obj.obj V := by
  refine CommRingCat.ofHom
    { toFun := fun a ↦ (a, ((differentials T).quotient.val.app V)
        (((d[T.obj.1.thickeningToBase.toShHom]).app V).d a))
      map_zero' := ?_, map_one' := ?_, map_add' := ?_, map_mul' := ?_ }
  all_goals sorry

/-- The universal divided-power Taylor section of the square-zero projection. -/
def differentialLift : T.obj.1.thickening.sheaf ⟶ sheaf T :=
  ObjectProperty.homMk { app := differentialLiftApp T, naturality := by sorry }

/-- A lift into the split extension defines a presheafed-space morphism over the identity. -/
def retractionToHom (lift : T.obj.1.thickening.sheaf ⟶ sheaf T) :
    (scheme T).toPresheafedSpace ⟶ T.obj.1.thickening.toPresheafedSpace where
  base := 𝟙 T.obj.1.thickening.toTopCat
  c := lift.hom

/-- A section of a square-zero projection induces local homomorphisms on stalks. -/
theorem retractionToHom_isLocalHom (lift : T.obj.1.thickening.sheaf ⟶ sheaf T)
    (h : lift ≫ projection T = 𝟙 _) (x : scheme T) :
    IsLocalHom ((retractionToHom T lift).stalkMap x).hom := sorry

/-- A section of the square-zero projection defines a scheme retraction. -/
def retraction (lift : T.obj.1.thickening.sheaf ⟶ sheaf T)
    (h : lift ≫ projection T = 𝟙 _) : scheme T ⟶ T.obj.1.thickening :=
  ⟨{ toHom := retractionToHom T lift, prop := retractionToHom_isLocalHom T lift h }⟩

/-- An affine open of the split extension is affine in the original scheme. -/
theorem baseOpen_isAffine (V : (scheme T).affineOpens) :
    (V.1 : T.obj.1.thickening.Opens) ∈ T.obj.1.thickening.affineOpens := sorry

/-- The affine open of the original scheme underlying an affine open of its split extension. -/
abbrev baseAffineOpen (V : (scheme T).affineOpens) : T.obj.1.thickening.affineOpens :=
  ⟨V.1, baseOpen_isAffine T V⟩

set_option backward.isDefEq.respectTransparency false in
/-- The full coordinate ideal consists of pairs whose function coordinate is in the original ideal. -/
def idealFamily (V : (scheme T).affineOpens) : Ideal Γ(scheme T, V) :=
  DividedPowers.TrivSqZeroExt.ideal ((differentials T).module.val.obj (op V.1))
    (T.obj.1.ideal.ideal (baseAffineOpen T V))

/-- The full coordinate ideals commute with localization on affine basic opens. -/
theorem idealFamily_map_basicOpen (V : (scheme T).affineOpens) (a : Γ(scheme T, V)) :
    (idealFamily T V).map
        ((scheme T).presheaf.map (homOfLE ((scheme T).basicOpen_le a)).op).hom =
      idealFamily T ((scheme T).affineBasicOpen a) := sorry

/-- The full divided-power ideal in the square-zero scheme. -/
def ideal : (scheme T).IdealSheafData where
  ideal := idealFamily T
  map_ideal_basicOpen := idealFamily_map_basicOpen T

set_option backward.isDefEq.respectTransparency false in
/-- The coordinate divided powers on the full ideal of the split extension. -/
def dividedPowers (V : (scheme T).affineOpens) : DividedPowers ((ideal T).ideal V) :=
  DividedPowers.TrivSqZeroExt.dividedPowers ((differentials T).module.val.obj (op V.1))
    (T.obj.1.gamma (baseAffineOpen T V))

/-- The coordinate divided powers commute with restriction to affine basic opens. -/
theorem dividedPowers_compatible : ∀ (V : (scheme T).affineOpens) (a : Γ(scheme T, V)),
    (dividedPowers T V).IsDPMorphism (dividedPowers T ((scheme T).affineBasicOpen a))
      ((scheme T).presheaf.map (homOfLE ((scheme T).basicOpen_le a)).op).hom := sorry

/-- The full coordinate ideal defines a divided-power thickening. -/
theorem isDividedPowerThickening : IsDividedPowerThickening (scheme T) (ideal T)
    (dividedPowers T) (dividedPowers_compatible T) := sorry

variable (I γ h_compatible x₀)

/-- The crystalline object of the split divided-power differential extension. -/
def crystallineObject : CRIS S I γ h_compatible X x₀ := by
  refine
    { source := T.obj.1.source
      thickening := scheme T
      thickeningToBase := retraction T (zeroLift T) (by
        apply ObjectProperty.hom_ext
        apply NatTrans.ext
        funext V
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro a
        rfl) ≫
        T.obj.1.thickeningToBase
      inclusion := T.obj.1.inclusion ≫ schemeInclusion T
      ideal := ideal T
      gamma := dividedPowers T
      thickening_compatible := dividedPowers_compatible T
      isThickening := isDividedPowerThickening T
      inclusion_isThickening := ?_, ideal_eq_ker := ?_, source_comm := ?_ }
  all_goals sorry

/-- The split differential extension is an object of the small crystalline site with the
original open source. -/
def smallObject : smallCrystallineSite S I γ h_compatible X x₀ := by
  refine ⟨⟨crystallineObject I γ h_compatible x₀ T, ?_⟩, ?_⟩
  all_goals sorry

/-- The canonical first-order crystalline thickening by divided-power differentials. -/
def object : smallCrystallineSite S I γ h_compatible X x₀ :=
  smallObject I γ h_compatible x₀ T

/-- The crystalline inclusion induced by the function-coordinate projection. -/
def inclusion : T ⟶ object I γ h_compatible x₀ T := by
  refine ObjectProperty.homMk
    { source := 𝟙 T.obj.1.source
      thickening := schemeInclusion T
      source_comm := ?_, base_comm := ?_, ideal_compatible := ?_,
      dividedPowers_compatible := ?_ }
  all_goals sorry

/-- The crystalline retraction induced by the constant section. -/
def p₀ : object I γ h_compatible x₀ T ⟶ T := by
  refine ObjectProperty.homMk
    { source := 𝟙 T.obj.1.source
      thickening := retraction T (zeroLift T) (by
        apply ObjectProperty.hom_ext
        apply NatTrans.ext
        funext V
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro a
        rfl)
      source_comm := ?_, base_comm := ?_, ideal_compatible := ?_,
      dividedPowers_compatible := ?_ }
  all_goals sorry

/-- The crystalline retraction induced by the universal divided-power Taylor section. -/
def p₁ : object I γ h_compatible x₀ T ⟶ T := by
  refine ObjectProperty.homMk
    { source := 𝟙 T.obj.1.source
      thickening := retraction T (differentialLift T) (by
        apply ObjectProperty.hom_ext
        apply NatTrans.ext
        funext V
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro a
        rfl)
      source_comm := ?_, base_comm := ?_, ideal_compatible := ?_,
      dividedPowers_compatible := ?_ }
  all_goals sorry

/-- The crystalline inclusion is a first-order thickening of schemes. -/
theorem isFirstOrder : IsFirstOrderThickening (inclusion I γ h_compatible x₀ T).hom.thickening :=
  sorry

/-- The constant retraction composed with the crystalline inclusion is the identity. -/
theorem p₀_comp_inclusion : inclusion I γ h_compatible x₀ T ≫ p₀ I γ h_compatible x₀ T =
    𝟙 T := sorry

/-- The Taylor retraction composed with the crystalline inclusion is the identity. -/
theorem p₁_comp_inclusion : inclusion I γ h_compatible x₀ T ≫ p₁ I γ h_compatible x₀ T =
    𝟙 T := sorry

variable {I γ h_compatible x₀}

/-- Every section of the split extension is the pair of its two coordinates. -/
theorem sheaf_apply (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ)
    (z : (sheaf T).obj.obj V) : z = (z.1, z.2) := rfl

/-- Membership in the full ideal is membership of the function coordinate in the original ideal. -/
theorem mem_ideal_iff (V : (scheme T).affineOpens) (z : Γ(scheme T, V)) :
    z ∈ (ideal T).ideal V ↔ z.1 ∈ T.obj.1.ideal.ideal (baseAffineOpen T V) := Iff.rfl

/-- The kernel of the projection consists exactly of pairs with zero function coordinate. -/
theorem ideal_eq (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ)
    (z : (sheaf T).obj.obj V) :
    z ∈ KernelIdeal.sectionIdeal (projection T) V ↔ z.1 = 0 := Iff.rfl

set_option backward.isDefEq.respectTransparency false in
/-- At a positive index, the divided powers act by the original power on the function coordinate
and its predecessor on the differential coordinate. -/
theorem dividedPowers_apply (V : (scheme T).affineOpens) (n : ℕ+)
    (z : (ideal T).ideal V) :
    (dividedPowers T V).dpow n z.1 =
      ((T.obj.1.gamma (baseAffineOpen T V)).dpow n z.1.1,
        (T.obj.1.gamma (baseAffineOpen T V)).dpow ((n : ℕ) - 1) z.1.1 • z.1.2) := sorry

/-- The difference between the Taylor and constant sections is the universal divided-power
derivation followed by inclusion of the differential coordinate. -/
theorem p₁_sub_p₀ (V : (Opens T.obj.1.thickening.toTopCat)ᵒᵖ)
    (a : T.obj.1.thickening.presheaf.obj V) :
    (differentialLift T).hom.app V a - (zeroLift T).hom.app V a =
      (0, (differentials T).quotient.val.app V
        (((d[T.obj.1.thickeningToBase.toShHom]).app V).d a)) := sorry

/-- On compatible affine opens, the Taylor section agrees with the ring-level divided-power
Taylor homomorphism under the derivation-compatible comparison of differentials. -/
theorem affine_taylorHom (W : T.obj.1.thickening.affineOpens) (V : S.affineOpens)
    (hWV : W.1 ≤ T.obj.1.thickeningToBase ⁻¹ᵁ V.1) :
    -- Local instance justification (defeq pin): the algebra is induced by the explicit affine section morphism, keeping the differential comparison definitionally aligned.
    letI := (T.obj.1.thickeningToBase.appLE V.1 W.1 hWV).hom.toAlgebra
    ∃! eΩ : Γ((differentials T).module, W.1) ≃ₗ[Γ(T.obj.1.thickening, W.1)]
        KaehlerDifferential.DeRham.dividedPowerDifferential
          (T.obj.1.thickeningToBase.appLE V.1 W.1 hWV).hom (T.obj.1.gamma W),
      ∀ a : Γ(T.obj.1.thickening, W.1),
        (TrivSqZeroExt.inl a + TrivSqZeroExt.inr
          (eΩ (((differentialLiftApp T (op W.1)) a).2))) =
        DividedPowerDifferential.taylorHom
          (T.obj.1.thickeningToBase.appLE V.1 W.1 hWV).hom (T.obj.1.gamma W) a := sorry

/-- The differential-coordinate inclusion identifies divided-power differentials with the
kernel module of the square-zero projection; its inverse extracts the differential coordinate. -/
def kernelIso : (differentials T).module ≅
    Scheme.SquareZeroExtension.kernelModule (sheaf T) (projection T)
      (projection_isSquareZero T) := by
  let K := Scheme.SquareZeroExtension.kernelModule
    (sheaf T) (projection T) (projection_isSquareZero T)
  let e := KernelIdeal.IsSquareZero.targetModuleForgetIso
    (π := projection T) (projection_isSquareZero T)
    (KernelIdeal.quotientComparison_isIso (projection T))
  refine
    { hom := ⟨{
        app := fun V ↦ (ModuleCat.homEquiv
          (M := (differentials T).module.val.obj V) (N := K.val.obj V)).symm
          { toFun := fun ω ↦ e.inv.hom.app V
              ((KernelIdeal.sectionsIso (projection T) V).inv
                ⟨(0, ω), by rfl⟩)
            map_add' := ?_, map_smul' := ?_ }
        naturality := ?_ }⟩
      inv := ⟨{
        app := fun V ↦ (ModuleCat.homEquiv
          (M := K.val.obj V) (N := (differentials T).module.val.obj V)).symm
          { toFun := fun ω ↦ (KernelIdeal.ιApp (projection T) V
              (e.hom.hom.app V ω)).2
            map_add' := ?_, map_smul' := ?_ }
        naturality := ?_ }⟩
      hom_inv_id := ?_, inv_hom_id := ?_ }
  all_goals sorry

end CrystallineObject.DividedPowerFirstOrderThickening
