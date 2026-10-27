/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.SecondOrderDifferential
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.DividedPower.DeRham
public import ReasLib.AlgebraicGeometry.Crystalline.FirstOrder

/-!
# Second-order divided-power crystalline thickenings

The two-direction extension by divided-power relative differentials and their exterior
two-forms is a crystalline thickening. The constant, Taylor, and diagonal sections give
three retractions to the original thickening and three to its first-order extension.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Crystalline
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace CrystallineObject.DividedPowerSecondOrderThickening

variable {S : Scheme.{u}} {I : S.IdealSheafData}
  {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
  {h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
  {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
  (T : smallCrystallineSite S I γ h_compatible X x₀)

/-- The divided-power scheme underlying a crystalline thickening. -/
def dividedPowerScheme : DividedPowerScheme.{u} where
  scheme := T.obj.1.thickening
  ideal := T.obj.1.ideal
  quasiCoherent := DividedPowerFirstOrderThickening.ideal_isQuasicoherent T
  dividedPowers := T.obj.1.gamma
  compatible := T.obj.1.thickening_compatible

/-- The second exterior-power sheaf of the divided-power differential module. -/
abbrev twoForms := DividedPowerScheme.RelativeDifferentials.twoForms
  (dividedPowerScheme T) S T.obj.1.thickeningToBase

/-- Exterior multiplication on sections of divided-power differential sheaves. -/
abbrev wedgeApp (V : (Opens T.obj.1.thickening)ᵒᵖ) :=
  DividedPowerScheme.RelativeDifferentials.wedgeApp
    (dividedPowerScheme T) S T.obj.1.thickeningToBase V

/-- The ring of two-direction extension sections over an open. -/
def ring (V : (Opens T.obj.1.thickening)ᵒᵖ) : CommRingCat.{u} :=
  DividedPowers.SecondOrderDifferential.ring (wedgeApp T V)

/-- Restriction of extension sections acts separately on all four sheaf coordinates. -/
def mapFun {U V : (Opens T.obj.1.thickening)ᵒᵖ} (ρ : U ⟶ V) : ring T U → ring T V :=
  fun z ↦ DividedPowers.SecondOrderDifferential.ofCoordinates (wedgeApp T V)
    (T.obj.1.thickening.presheaf.map ρ z.1)
    ((DividedPowerFirstOrderThickening.differentials T).module.val.map ρ z.2.1.1)
    ((DividedPowerFirstOrderThickening.differentials T).module.val.map ρ z.2.1.2)
    ((twoForms T).val.map ρ z.2.2)

/-- Restriction preserves zero extension sections. -/
theorem mapFun_zero {U V : (Opens T.obj.1.thickening)ᵒᵖ} (ρ : U ⟶ V) :
    mapFun T ρ 0 = 0 := sorry

/-- Restriction preserves the unit extension section. -/
theorem mapFun_one {U V : (Opens T.obj.1.thickening)ᵒᵖ} (ρ : U ⟶ V) :
    mapFun T ρ 1 = 1 := sorry

/-- Restriction preserves addition of extension sections. -/
theorem mapFun_add {U V : (Opens T.obj.1.thickening)ᵒᵖ} (ρ : U ⟶ V)
    (a b : ring T U) : mapFun T ρ (a + b) = mapFun T ρ a + mapFun T ρ b := sorry

/-- Restriction preserves the cross-wedge multiplication of extension sections. -/
theorem mapFun_mul {U V : (Opens T.obj.1.thickening)ᵒᵖ} (ρ : U ⟶ V)
    (a b : ring T U) : mapFun T ρ (a * b) = mapFun T ρ a * mapFun T ρ b := sorry

/-- The ring homomorphism restricting two-direction extension sections. -/
def map {U V : (Opens T.obj.1.thickening)ᵒᵖ} (ρ : U ⟶ V) : ring T U ⟶ ring T V :=
  CommRingCat.ofHom
    { toFun := mapFun T ρ
      map_zero' := mapFun_zero T ρ
      map_one' := mapFun_one T ρ
      map_add' := mapFun_add T ρ
      map_mul' := mapFun_mul T ρ }

/-- Identity restrictions are identity ring homomorphisms. -/
theorem map_id (U : (Opens T.obj.1.thickening)ᵒᵖ) : map T (𝟙 U) = 𝟙 _ := sorry

/-- Restriction homomorphisms respect composition. -/
theorem map_comp {U V W : (Opens T.obj.1.thickening)ᵒᵖ} (ρ : U ⟶ V) (σ : V ⟶ W) :
    map T (ρ ≫ σ) = map T ρ ≫ map T σ := sorry

/-- The presheaf of two-direction extension rings. -/
def presheaf : (Opens T.obj.1.thickening)ᵒᵖ ⥤ CommRingCat.{u} where
  obj := ring T
  map := map T
  map_id := map_id T
  map_comp := map_comp T

/-- The presheaf of extension sections satisfies the sheaf condition. -/
theorem presheaf_isSheaf : Presheaf.IsSheaf
    (Opens.grothendieckTopology T.obj.1.thickening) (presheaf T) := sorry

/-- The structure sheaf of the two-direction extension. -/
def sheaf : TopCat.Sheaf CommRingCat.{u} T.obj.1.thickening.toTopCat :=
  ⟨presheaf T, presheaf_isSheaf T⟩

/-- The sectionwise projection to functions. -/
def projectionApp (V : (Opens T.obj.1.thickening)ᵒᵖ) :
    (sheaf T).obj.obj V ⟶ T.obj.1.thickening.presheaf.obj V :=
  CommRingCat.ofHom (DividedPowers.SecondOrderDifferential.projection (wedgeApp T V))

/-- Projection to functions commutes with restriction. -/
theorem projection_naturality {U V : (Opens T.obj.1.thickening)ᵒᵖ} (ρ : U ⟶ V) :
    (sheaf T).obj.map ρ ≫ projectionApp T V =
      projectionApp T U ≫ T.obj.1.thickening.presheaf.map ρ := sorry

/-- The function-coordinate projection of ring sheaves. -/
def projection : sheaf T ⟶ T.obj.1.thickening.sheaf :=
  ObjectProperty.homMk
    { app := projectionApp T
      naturality := fun {_ _} ρ ↦ projection_naturality T ρ }

/-- The function-coordinate projection is locally surjective. -/
instance projection_isLocallySurjective :
    CategoryTheory.Sheaf.IsLocallySurjective (projection T) := sorry

/-- Stalk rings of the extension sheaf are local. -/
instance stalk_isLocalRing (x : T.obj.1.thickening) :
    IsLocalRing ((sheaf T).presheaf.stalk x) := sorry

/-- The locally ringed space carried by the extension sheaf on the original topological space. -/
def locallyRingedSpace : LocallyRingedSpace.{u} where
  toSheafedSpace :=
    { carrier := T.obj.1.thickening.toTopCat
      presheaf := (sheaf T).presheaf
      IsSheaf := (sheaf T).2 }
  isLocalRing := stalk_isLocalRing T

/-- The two-direction locally ringed space has affine neighbourhoods. -/
theorem locallyRingedSpace_local_affine : ∀ x : locallyRingedSpace T,
    ∃ (U : OpenNhds x) (R : CommRingCat.{u}),
      Nonempty ((locallyRingedSpace T).restrict U.isOpenEmbedding ≅
        Spec.toLocallyRingedSpace.obj (op R)) := sorry

/-- The scheme with the two-direction divided-power differential extension as structure sheaf. -/
def scheme : Scheme.{u} where
  toLocallyRingedSpace := locallyRingedSpace T
  local_affine := locallyRingedSpace_local_affine T

/-- The inclusion of presheafed spaces induced by the function projection. -/
def schemeInclusionToHom :
    T.obj.1.thickening.toPresheafedSpace ⟶ (scheme T).toPresheafedSpace where
  base := 𝟙 T.obj.1.thickening.toTopCat
  c := (projection T).hom

/-- The inclusion induced by projection is local on stalks. -/
theorem schemeInclusionToHom_isLocalHom (x : T.obj.1.thickening) :
    IsLocalHom ((schemeInclusionToHom T).stalkMap x).hom := sorry

/-- The inclusion of the original scheme into the two-direction extension. -/
def schemeInclusion : T.obj.1.thickening ⟶ scheme T :=
  ⟨{ toHom := schemeInclusionToHom T
     prop := schemeInclusionToHom_isLocalHom T }⟩

/-- An affine open of the extension is affine on the original scheme. -/
theorem baseOpen_isAffine (V : (scheme T).affineOpens) :
    (V.1 : T.obj.1.thickening.Opens) ∈ T.obj.1.thickening.affineOpens := sorry

/-- The affine open of the original scheme with the same underlying open as an extension open. -/
def baseAffineOpen (V : (scheme T).affineOpens) : T.obj.1.thickening.affineOpens :=
  ⟨V.1, baseOpen_isAffine T V⟩

/-- The extension ring on an affine open. -/
abbrev affineSection (V : (scheme T).affineOpens) : Type u :=
  (presheaf T).obj (op V.1)

/-- The function-coordinate ring homomorphism on affine sections. -/
def projectionHom (V : (scheme T).affineOpens) :
    Γ(scheme T, V) →+* Γ(T.obj.1.thickening, baseAffineOpen T V) :=
  (projectionApp T (op V.1)).hom

/-- The full coordinate ideal on an affine open. -/
def idealFamily (V : (scheme T).affineOpens) : Ideal Γ(scheme T, V) :=
  (T.obj.1.ideal.ideal (baseAffineOpen T V)).comap (projectionHom T V)

/-- The full coordinate ideals commute with localization on affine basic opens. -/
theorem idealFamily_map_basicOpen (V : (scheme T).affineOpens) (a : Γ(scheme T, V)) :
    (idealFamily T V).map
      ((scheme T).presheaf.map (homOfLE ((scheme T).basicOpen_le a)).op).hom =
        idealFamily T ((scheme T).affineBasicOpen a) := sorry

/-- The inverse-image ideal sheaf of the original divided-power ideal. -/
def ideal : (scheme T).IdealSheafData where
  ideal := idealFamily T
  map_ideal_basicOpen := idealFamily_map_basicOpen T

/-- Full coordinate ideal membership is original ideal membership of the function coordinate. -/
theorem mem_ideal_iff (V : (scheme T).affineOpens) (z : Γ(scheme T, V)) :
    z ∈ (ideal T).ideal V ↔ z.1 ∈ T.obj.1.ideal.ideal (baseAffineOpen T V) := Iff.rfl

/-- The coordinate divided powers on the full inverse-image ideal. -/
def dividedPowers (V : (scheme T).affineOpens) : DividedPowers ((ideal T).ideal V) :=
  DividedPowers.SecondOrderDifferential.dividedPowers (wedgeApp T (op V.1))
    (T.obj.1.gamma (baseAffineOpen T V))

set_option backward.isDefEq.respectTransparency false in
/-- Divided powers act on four coordinates by the original powers and their two predecessors. -/
theorem dividedPowers_apply (V : (scheme T).affineOpens) (n : ℕ)
    (z : (ideal T).ideal V) :
    (dividedPowers T V).dpow n z.1 =
      DividedPowers.SecondOrderDifferential.ofCoordinates (wedgeApp T (op V.1))
        ((T.obj.1.gamma (baseAffineOpen T V)).dpow n z.1.1)
        (DividedPowers.BilinearExtension.dpowPred
          (T.obj.1.gamma (baseAffineOpen T V)) n z.1.1 • z.1.2.1.1)
        (DividedPowers.BilinearExtension.dpowPred
          (T.obj.1.gamma (baseAffineOpen T V)) n z.1.1 • z.1.2.1.2)
        (DividedPowers.BilinearExtension.dpowPred
          (T.obj.1.gamma (baseAffineOpen T V)) n z.1.1 • z.1.2.2 +
          DividedPowers.BilinearExtension.dpowPredTwo
            (T.obj.1.gamma (baseAffineOpen T V)) n z.1.1 •
              wedgeApp T (op V.1) z.1.2.1.1 z.1.2.1.2) :=
  DividedPowers.SecondOrderDifferential.dividedPowers_apply _ _ n z.1.1 z.2
    z.1.2.1.1 z.1.2.1.2 z.1.2.2

/-- The coordinate divided powers commute with restriction to affine basic opens. -/
theorem dividedPowers_compatible : ∀ (V : (scheme T).affineOpens) (a : Γ(scheme T, V)),
    (dividedPowers T V).IsDPMorphism (dividedPowers T ((scheme T).affineBasicOpen a))
      ((scheme T).presheaf.map (homOfLE ((scheme T).basicOpen_le a)).op).hom := sorry

/-- The full ideal with coordinate powers defines a divided-power thickening. -/
theorem isDividedPowerThickening : IsDividedPowerThickening (scheme T) (ideal T)
    (dividedPowers T) (dividedPowers_compatible T) := sorry

/-- The constant section has all three differential coordinates zero. -/
def q0Fun (V : (Opens T.obj.1.thickening)ᵒᵖ) :
    T.obj.1.thickening.presheaf.obj V → ring T V :=
  fun a ↦ DividedPowers.SecondOrderDifferential.ofCoordinates (wedgeApp T V) a 0 0 0

/-- The first Taylor section differentiates into the first direction. -/
def q1Fun (V : (Opens T.obj.1.thickening)ᵒᵖ) :
    T.obj.1.thickening.presheaf.obj V → ring T V :=
  fun a ↦ DividedPowers.SecondOrderDifferential.ofCoordinates (wedgeApp T V) a
    (DividedPowerScheme.RelativeDifferentials.derivationApp
      (dividedPowerScheme T) S T.obj.1.thickeningToBase V a) 0 0

/-- The diagonal Taylor section differentiates into both directions. -/
def q2Fun (V : (Opens T.obj.1.thickening)ᵒᵖ) :
    T.obj.1.thickening.presheaf.obj V → ring T V :=
  fun a ↦ DividedPowers.SecondOrderDifferential.ofCoordinates (wedgeApp T V) a
    (DividedPowerScheme.RelativeDifferentials.derivationApp
      (dividedPowerScheme T) S T.obj.1.thickeningToBase V a)
    (DividedPowerScheme.RelativeDifferentials.derivationApp
      (dividedPowerScheme T) S T.obj.1.thickeningToBase V a) 0

/-- The first-direction map includes the first-order module coordinate in the first direction. -/
def q01Fun (V : (Opens T.obj.1.thickening)ᵒᵖ) :
    (DividedPowerFirstOrderThickening.sheaf T).obj.obj V → ring T V :=
  fun z ↦ DividedPowers.SecondOrderDifferential.ofCoordinates (wedgeApp T V) z.1 z.2 0 0

/-- The middle map uses the universal derivation and the degree-one de Rham differential. -/
def q12Fun (V : (Opens T.obj.1.thickening)ᵒᵖ) :
    (DividedPowerFirstOrderThickening.sheaf T).obj.obj V → ring T V :=
  fun z ↦ DividedPowers.SecondOrderDifferential.ofCoordinates (wedgeApp T V) z.1
    (DividedPowerScheme.RelativeDifferentials.derivationApp
      (dividedPowerScheme T) S T.obj.1.thickeningToBase V z.1) z.2
    (DividedPowerScheme.RelativeDifferentials.dApp
      (dividedPowerScheme T) S T.obj.1.thickeningToBase V z.2)

/-- The diagonal map repeats the first-order module coordinate. -/
def q02Fun (V : (Opens T.obj.1.thickening)ᵒᵖ) :
    (DividedPowerFirstOrderThickening.sheaf T).obj.obj V → ring T V :=
  fun z ↦ DividedPowers.SecondOrderDifferential.ofCoordinates (wedgeApp T V) z.1 z.2 z.2 0

/-- The constant section as a ring homomorphism. -/
def q0App (V : (Opens T.obj.1.thickening)ᵒᵖ) :
    T.obj.1.thickening.presheaf.obj V ⟶ ring T V :=
  CommRingCat.ofHom (DividedPowers.BilinearExtension.inclusion
    (DividedPowers.SecondOrderDifferential.crossPairing (wedgeApp T V)))

/-- The first-direction map as a ring homomorphism. -/
def q01App (V : (Opens T.obj.1.thickening)ᵒᵖ) :
    (DividedPowerFirstOrderThickening.sheaf T).obj.obj V ⟶ ring T V :=
  CommRingCat.ofHom (DividedPowers.SecondOrderDifferential.q01 (wedgeApp T V))

/-- The diagonal map as a ring homomorphism. -/
def q02App (V : (Opens T.obj.1.thickening)ᵒᵖ) :
    (DividedPowerFirstOrderThickening.sheaf T).obj.obj V ⟶ ring T V :=
  CommRingCat.ofHom (DividedPowers.SecondOrderDifferential.q02 (wedgeApp T V)
    (DividedPowerScheme.RelativeDifferentials.wedgeApp_alternating
      (dividedPowerScheme T) S T.obj.1.thickeningToBase V))

/-- The middle map as a ring homomorphism. -/
def q12App (V : (Opens T.obj.1.thickening)ᵒᵖ) :
    (DividedPowerFirstOrderThickening.sheaf T).obj.obj V ⟶ ring T V := by
  refine CommRingCat.ofHom
    { toFun := q12Fun T V
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_ }
  all_goals sorry

/-- The first Taylor section as a ring homomorphism. -/
def q1App (V : (Opens T.obj.1.thickening)ᵒᵖ) :
    T.obj.1.thickening.presheaf.obj V ⟶ ring T V :=
  DividedPowerFirstOrderThickening.differentialLiftApp T V ≫ q01App T V

/-- The diagonal Taylor section as a ring homomorphism. -/
def q2App (V : (Opens T.obj.1.thickening)ᵒᵖ) :
    T.obj.1.thickening.presheaf.obj V ⟶ ring T V :=
  DividedPowerFirstOrderThickening.differentialLiftApp T V ≫ q02App T V

/-- The coordinate map q0 commutes with restriction of sections. -/
theorem q0_naturality {U V : (Opens T.obj.1.thickening)ᵒᵖ} (ρ : U ⟶ V) :
    T.obj.1.thickening.sheaf.obj.map ρ ≫ q0App T V =
      q0App T U ≫ (sheaf T).obj.map ρ := sorry

/-- The coordinate map q0 as a morphism of ring sheaves. -/
def q0 : T.obj.1.thickening.sheaf ⟶ sheaf T :=
  ObjectProperty.homMk
    { app := q0App T
      naturality := fun {_ _} ρ ↦ q0_naturality T ρ }

/-- The coordinate map q1 commutes with restriction of sections. -/
theorem q1_naturality {U V : (Opens T.obj.1.thickening)ᵒᵖ} (ρ : U ⟶ V) :
    T.obj.1.thickening.sheaf.obj.map ρ ≫ q1App T V =
      q1App T U ≫ (sheaf T).obj.map ρ := sorry

/-- The coordinate map q1 as a morphism of ring sheaves. -/
def q1 : T.obj.1.thickening.sheaf ⟶ sheaf T :=
  ObjectProperty.homMk
    { app := q1App T
      naturality := fun {_ _} ρ ↦ q1_naturality T ρ }

/-- The coordinate map q2 commutes with restriction of sections. -/
theorem q2_naturality {U V : (Opens T.obj.1.thickening)ᵒᵖ} (ρ : U ⟶ V) :
    T.obj.1.thickening.sheaf.obj.map ρ ≫ q2App T V =
      q2App T U ≫ (sheaf T).obj.map ρ := sorry

/-- The coordinate map q2 as a morphism of ring sheaves. -/
def q2 : T.obj.1.thickening.sheaf ⟶ sheaf T :=
  ObjectProperty.homMk
    { app := q2App T
      naturality := fun {_ _} ρ ↦ q2_naturality T ρ }

/-- The coordinate map q01 commutes with restriction of sections. -/
theorem q01_naturality {U V : (Opens T.obj.1.thickening)ᵒᵖ} (ρ : U ⟶ V) :
    (DividedPowerFirstOrderThickening.sheaf T).obj.map ρ ≫ q01App T V =
      q01App T U ≫ (sheaf T).obj.map ρ := sorry

/-- The coordinate map q01 as a morphism of ring sheaves. -/
def q01 : (DividedPowerFirstOrderThickening.sheaf T) ⟶ sheaf T :=
  ObjectProperty.homMk
    { app := q01App T
      naturality := fun {_ _} ρ ↦ q01_naturality T ρ }

/-- The coordinate map q12 commutes with restriction of sections. -/
theorem q12_naturality {U V : (Opens T.obj.1.thickening)ᵒᵖ} (ρ : U ⟶ V) :
    (DividedPowerFirstOrderThickening.sheaf T).obj.map ρ ≫ q12App T V =
      q12App T U ≫ (sheaf T).obj.map ρ := sorry

/-- The coordinate map q12 as a morphism of ring sheaves. -/
def q12 : (DividedPowerFirstOrderThickening.sheaf T) ⟶ sheaf T :=
  ObjectProperty.homMk
    { app := q12App T
      naturality := fun {_ _} ρ ↦ q12_naturality T ρ }

/-- The coordinate map q02 commutes with restriction of sections. -/
theorem q02_naturality {U V : (Opens T.obj.1.thickening)ᵒᵖ} (ρ : U ⟶ V) :
    (DividedPowerFirstOrderThickening.sheaf T).obj.map ρ ≫ q02App T V =
      q02App T U ≫ (sheaf T).obj.map ρ := sorry

/-- The coordinate map q02 as a morphism of ring sheaves. -/
def q02 : (DividedPowerFirstOrderThickening.sheaf T) ⟶ sheaf T :=
  ObjectProperty.homMk
    { app := q02App T
      naturality := fun {_ _} ρ ↦ q02_naturality T ρ }

/-- A section of the function projection induces a scheme retraction. -/
def retraction (lift : T.obj.1.thickening.sheaf ⟶ sheaf T)
    (h : lift ≫ projection T = 𝟙 _) : scheme T ⟶ T.obj.1.thickening :=
  ⟨{ toHom := { base := 𝟙 T.obj.1.thickening.toTopCat, c := lift.hom }
     prop := fun _ ↦ by sorry }⟩

/-- A sheaf morphism compatible with both function projections induces a scheme morphism
from the second-order extension to the first-order extension. -/
def retractionFirstOrder (lift : DividedPowerFirstOrderThickening.sheaf T ⟶ sheaf T)
    (h : lift ≫ projection T = DividedPowerFirstOrderThickening.projection T) :
    scheme T ⟶ DividedPowerFirstOrderThickening.scheme T :=
  ⟨{ toHom := { base := 𝟙 T.obj.1.thickening.toTopCat, c := lift.hom }
     prop := fun _ ↦ by sorry }⟩

/-- The scheme morphism induced by the coordinate map q0. -/
def q0Scheme : scheme T ⟶ T.obj.1.thickening :=
  retraction T (q0 T) (by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext V
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rfl)

/-- The scheme morphism induced by the coordinate map q1. -/
def q1Scheme : scheme T ⟶ T.obj.1.thickening :=
  retraction T (q1 T) (by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext V
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rfl)

/-- The scheme morphism induced by the coordinate map q2. -/
def q2Scheme : scheme T ⟶ T.obj.1.thickening :=
  retraction T (q2 T) (by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext V
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rfl)

/-- The scheme morphism induced by the coordinate map q01. -/
def q01Scheme : scheme T ⟶ DividedPowerFirstOrderThickening.scheme T :=
  retractionFirstOrder T (q01 T) (by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext V
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rfl)

/-- The scheme morphism induced by the coordinate map q12. -/
def q12Scheme : scheme T ⟶ DividedPowerFirstOrderThickening.scheme T :=
  retractionFirstOrder T (q12 T) (by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext V
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rfl)

/-- The scheme morphism induced by the coordinate map q02. -/
def q02Scheme : scheme T ⟶ DividedPowerFirstOrderThickening.scheme T :=
  retractionFirstOrder T (q02 T) (by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext V
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rfl)

/-- The scheme morphism q0 preserves divided powers on every compatible pair of affine opens. -/
theorem q0_isDPMorphism :
    ∀ (V : T.obj.1.thickening.affineOpens) (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ q0Scheme T ⁻¹ᵁ V.1),
      (T.obj.1.gamma V).IsDPMorphism (dividedPowers T W)
        ((q0Scheme T).appLE V W hVW).hom := sorry

/-- The scheme morphism q1 preserves divided powers on every compatible pair of affine opens. -/
theorem q1_isDPMorphism :
    ∀ (V : T.obj.1.thickening.affineOpens) (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ q1Scheme T ⁻¹ᵁ V.1),
      (T.obj.1.gamma V).IsDPMorphism (dividedPowers T W)
        ((q1Scheme T).appLE V W hVW).hom := sorry

/-- The scheme morphism q2 preserves divided powers on every compatible pair of affine opens. -/
theorem q2_isDPMorphism :
    ∀ (V : T.obj.1.thickening.affineOpens) (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ q2Scheme T ⁻¹ᵁ V.1),
      (T.obj.1.gamma V).IsDPMorphism (dividedPowers T W)
        ((q2Scheme T).appLE V W hVW).hom := sorry

/-- The scheme morphism q01 preserves divided powers on every compatible pair of affine opens. -/
theorem q01_isDPMorphism :
    ∀ (V : (DividedPowerFirstOrderThickening.scheme T).affineOpens) (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ q01Scheme T ⁻¹ᵁ V.1),
      (DividedPowerFirstOrderThickening.dividedPowers T V).IsDPMorphism (dividedPowers T W)
        ((q01Scheme T).appLE V W hVW).hom := sorry

/-- The scheme morphism q12 preserves divided powers on every compatible pair of affine opens. -/
theorem q12_isDPMorphism :
    ∀ (V : (DividedPowerFirstOrderThickening.scheme T).affineOpens) (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ q12Scheme T ⁻¹ᵁ V.1),
      (DividedPowerFirstOrderThickening.dividedPowers T V).IsDPMorphism (dividedPowers T W)
        ((q12Scheme T).appLE V W hVW).hom := sorry

/-- The scheme morphism q02 preserves divided powers on every compatible pair of affine opens. -/
theorem q02_isDPMorphism :
    ∀ (V : (DividedPowerFirstOrderThickening.scheme T).affineOpens) (W : (scheme T).affineOpens)
      (hVW : W.1 ≤ q02Scheme T ⁻¹ᵁ V.1),
      (DividedPowerFirstOrderThickening.dividedPowers T V).IsDPMorphism (dividedPowers T W)
        ((q02Scheme T).appLE V W hVW).hom := sorry

/-- The middle coordinate map preserves multiplication. -/
theorem q12_map_mul (V : (Opens T.obj.1.thickening)ᵒᵖ)
    (a b : (DividedPowerFirstOrderThickening.sheaf T).obj.obj V) :
    q12App T V (a * b) = q12App T V a * q12App T V b := (q12App T V).hom.map_mul a b

/-- The middle scheme map commutes with divided powers of affine ideal sections. -/
theorem q12_map_dpow (V : (DividedPowerFirstOrderThickening.scheme T).affineOpens)
    (W : (scheme T).affineOpens) (hVW : W.1 ≤ q12Scheme T ⁻¹ᵁ V.1)
    (n : ℕ) (a : Γ(DividedPowerFirstOrderThickening.scheme T, V))
    (ha : a ∈ (DividedPowerFirstOrderThickening.ideal T).ideal V) :
    (dividedPowers T W).dpow n (((q12Scheme T).appLE V W hVW) a) =
      ((q12Scheme T).appLE V W hVW)
        ((DividedPowerFirstOrderThickening.dividedPowers T V).dpow n a) :=
  (q12_isDPMorphism T V W hVW).dpow_comp a ha

/-- The inclusion of the source commutes with the structure morphism to the base. -/
theorem source_comm : T.obj.1.inclusion ≫ schemeInclusion T ≫
    (q0Scheme T ≫ T.obj.1.thickeningToBase) =
      T.obj.1.source.hom ≫ x₀ ≫ I.subschemeι := sorry

/-- The source inclusion is a thickening whose kernel is the full coordinate ideal. -/
theorem inclusion_spec : IsThickening (T.obj.1.inclusion ≫ schemeInclusion T) ∧
    ideal T = (T.obj.1.inclusion ≫ schemeInclusion T).ker := sorry

variable (I γ h_compatible x₀)

/-- The crystalline object with the two-direction extension scheme and coordinate divided powers. -/
def crystallineObject : CRIS S I γ h_compatible X x₀ :=
  CrystallineObject.of I γ h_compatible X x₀ T.obj.1.source
    (scheme T) (q0Scheme T ≫ T.obj.1.thickeningToBase)
    (T.obj.1.inclusion ≫ schemeInclusion T)
    (ideal T) (dividedPowers T) (dividedPowers_compatible T)
    (isDividedPowerThickening T) (inclusion_spec T).1 (inclusion_spec T).2 (source_comm T)

/-- The second-order crystalline object is compatible with the base divided powers. -/
theorem crystallineObject_baseCompatible :
    CrystallineBaseCompatible I γ h_compatible x₀
      (crystallineObject I γ h_compatible x₀ T) := sorry

/-- The source of the second-order crystalline object remains an open subscheme. -/
theorem sourceIsOpen : IsOpenImmersion
    (crystallineObject I γ h_compatible x₀ T).source.hom := T.property

/-- The second-order extension as an object of the small crystalline site. -/
def object : smallCrystallineSite S I γ h_compatible X x₀ :=
  ⟨⟨crystallineObject I γ h_compatible x₀ T,
      crystallineObject_baseCompatible I γ h_compatible x₀ T⟩,
    sourceIsOpen I γ h_compatible x₀ T⟩

/-- The constant retraction commutes with the source inclusion. -/
theorem q0_source_comm :
    (𝟙 T.obj.1.source : T.obj.1.source ⟶ T.obj.1.source).left ≫ T.obj.1.inclusion =
      (crystallineObject I γ h_compatible x₀ T).inclusion ≫ q0Scheme T := sorry

/-- The constant retraction commutes with the morphism to the base. -/
theorem q0_base_comm : q0Scheme T ≫ T.obj.1.thickeningToBase =
    (crystallineObject I γ h_compatible x₀ T).thickeningToBase := sorry

/-- The constant retraction preserves the defining ideals. -/
theorem q0_ideal_compatible : T.obj.1.ideal.comap (q0Scheme T) ≤ ideal T := sorry

/-- The constant retraction as a crystalline homomorphism. -/
def q0Hom : CrystallineObject.Hom (object I γ h_compatible x₀ T).obj.1 T.obj.1 where
  source := 𝟙 T.obj.1.source
  thickening := q0Scheme T
  source_comm := q0_source_comm I γ h_compatible x₀ T
  base_comm := q0_base_comm I γ h_compatible x₀ T
  ideal_compatible := q0_ideal_compatible I γ h_compatible x₀ T
  dividedPowers_compatible := q0_isDPMorphism T

/-- The coordinate morphism q1 as a crystalline homomorphism. -/
def q1Hom : CrystallineObject.Hom (object I γ h_compatible x₀ T).obj.1
    T.obj.1 := by
  refine {
    source := 𝟙 T.obj.1.source
    thickening := q1Scheme T
    source_comm := ?_
    base_comm := ?_
    ideal_compatible := ?_
    dividedPowers_compatible := q1_isDPMorphism T }
  all_goals sorry

/-- The coordinate morphism q2 as a crystalline homomorphism. -/
def q2Hom : CrystallineObject.Hom (object I γ h_compatible x₀ T).obj.1
    T.obj.1 := by
  refine {
    source := 𝟙 T.obj.1.source
    thickening := q2Scheme T
    source_comm := ?_
    base_comm := ?_
    ideal_compatible := ?_
    dividedPowers_compatible := q2_isDPMorphism T }
  all_goals sorry

/-- The coordinate morphism q01 as a crystalline homomorphism. -/
def q01Hom : CrystallineObject.Hom (object I γ h_compatible x₀ T).obj.1
    (DividedPowerFirstOrderThickening.object I γ h_compatible x₀ T).obj.1 := by
  refine {
    source := 𝟙 T.obj.1.source
    thickening := q01Scheme T
    source_comm := ?_
    base_comm := ?_
    ideal_compatible := ?_
    dividedPowers_compatible := q01_isDPMorphism T }
  all_goals sorry

/-- The coordinate morphism q12 as a crystalline homomorphism. -/
def q12Hom : CrystallineObject.Hom (object I γ h_compatible x₀ T).obj.1
    (DividedPowerFirstOrderThickening.object I γ h_compatible x₀ T).obj.1 := by
  refine {
    source := 𝟙 T.obj.1.source
    thickening := q12Scheme T
    source_comm := ?_
    base_comm := ?_
    ideal_compatible := ?_
    dividedPowers_compatible := q12_isDPMorphism T }
  all_goals sorry

/-- The coordinate morphism q02 as a crystalline homomorphism. -/
def q02Hom : CrystallineObject.Hom (object I γ h_compatible x₀ T).obj.1
    (DividedPowerFirstOrderThickening.object I γ h_compatible x₀ T).obj.1 := by
  refine {
    source := 𝟙 T.obj.1.source
    thickening := q02Scheme T
    source_comm := ?_
    base_comm := ?_
    ideal_compatible := ?_
    dividedPowers_compatible := q02_isDPMorphism T }
  all_goals sorry

/-- The coordinate morphism q0 in the small crystalline site. -/
def q₀ : object I γ h_compatible x₀ T ⟶ T :=
  ObjectProperty.homMk (q0Hom I γ h_compatible x₀ T)

/-- The coordinate morphism q1 in the small crystalline site. -/
def q₁ : object I γ h_compatible x₀ T ⟶ T :=
  ObjectProperty.homMk (q1Hom I γ h_compatible x₀ T)

/-- The coordinate morphism q2 in the small crystalline site. -/
def q₂ : object I γ h_compatible x₀ T ⟶ T :=
  ObjectProperty.homMk (q2Hom I γ h_compatible x₀ T)

/-- The coordinate morphism q01 in the small crystalline site. -/
def q₀₁ : object I γ h_compatible x₀ T ⟶ DividedPowerFirstOrderThickening.object I γ h_compatible x₀ T :=
  ObjectProperty.homMk (q01Hom I γ h_compatible x₀ T)

/-- The coordinate morphism q12 in the small crystalline site. -/
def q₁₂ : object I γ h_compatible x₀ T ⟶ DividedPowerFirstOrderThickening.object I γ h_compatible x₀ T :=
  ObjectProperty.homMk (q12Hom I γ h_compatible x₀ T)

/-- The coordinate morphism q02 in the small crystalline site. -/
def q₀₂ : object I γ h_compatible x₀ T ⟶ DividedPowerFirstOrderThickening.object I γ h_compatible x₀ T :=
  ObjectProperty.homMk (q02Hom I γ h_compatible x₀ T)

/-- Composition of q01 with the first-order retraction p0 equals q0. -/
theorem q0_eq_q01_comp_p0 :
    q₀₁ I γ h_compatible x₀ T ≫
      DividedPowerFirstOrderThickening.p₀ I γ h_compatible x₀ T =
        q₀ I γ h_compatible x₀ T := sorry

/-- Composition of q01 with the first-order retraction p1 equals q1. -/
theorem q1_eq_q01_comp_p1 :
    q₀₁ I γ h_compatible x₀ T ≫
      DividedPowerFirstOrderThickening.p₁ I γ h_compatible x₀ T =
        q₁ I γ h_compatible x₀ T := sorry

/-- Composition of q12 with the first-order retraction p0 equals q1. -/
theorem q1_eq_q12_comp_p0 :
    q₁₂ I γ h_compatible x₀ T ≫
      DividedPowerFirstOrderThickening.p₀ I γ h_compatible x₀ T =
        q₁ I γ h_compatible x₀ T := sorry

/-- Composition of q12 with the first-order retraction p1 equals q2. -/
theorem q2_eq_q12_comp_p1 :
    q₁₂ I γ h_compatible x₀ T ≫
      DividedPowerFirstOrderThickening.p₁ I γ h_compatible x₀ T =
        q₂ I γ h_compatible x₀ T := sorry

/-- Composition of q02 with the first-order retraction p0 equals q0. -/
theorem q0_eq_q02_comp_p0 :
    q₀₂ I γ h_compatible x₀ T ≫
      DividedPowerFirstOrderThickening.p₀ I γ h_compatible x₀ T =
        q₀ I γ h_compatible x₀ T := sorry

/-- Composition of q02 with the first-order retraction p1 equals q2. -/
theorem q2_eq_q02_comp_p1 :
    q₀₂ I γ h_compatible x₀ T ≫
      DividedPowerFirstOrderThickening.p₁ I γ h_compatible x₀ T =
        q₂ I γ h_compatible x₀ T := sorry

end CrystallineObject.DividedPowerSecondOrderThickening
