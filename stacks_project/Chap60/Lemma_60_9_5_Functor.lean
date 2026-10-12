/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap60.Definition_60_9_1
public import stacks_project.Chap60.Remark_60_8_5_Functoriality_Functor

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

/- The inclusions of the open subschemes are represented by their scheme morphisms. -/
variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S S' X X' : Scheme.{u}}
variable (iX : X' ⟶ X) [IsOpenImmersion iX]

variable (I : S.IdealSheafData) (I' : S'.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (γ' : ∀ V : S'.affineOpens, DividedPowers (I'.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (g : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
      (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom)
variable (h'_compatible :
  ∀ (V : S'.affineOpens) (g : Γ(S', V)),
    (γ' V).IsDPMorphism (γ' (S'.affineBasicOpen g))
      (S'.presheaf.map (homOfLE (S'.basicOpen_le g)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (x₀ : X ⟶ I.subscheme) (x₀' : X' ⟶ I'.subscheme)
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (h_p' : ∀ U : X'.affineOpens, IsNilpotent (p : Γ(X', U)))

/- The divided-power morphism induced by the open base inclusion. -/
variable (g : DividedPowerSchemeHom I' I s' s)
variable (h_comm : iX ≫ x₀ = x₀' ≫ g.zeroFiberMap)
variable (h_dividedPowers :
  ∀ (V : S.affineOpens) (W : S'.affineOpens)
    (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
    (γ V).IsDPMorphism (γ' W) (g.base.appLE V W hVW).hom)

/-- The concrete crystalline functor induced by the two open immersions. -/
abbrev openCrystallineFunctor :
    CrystallineFunctor I' I γ' γ h'_compatible h_compatible s' s
      x₀' x₀ iX g h_comm :=
  CrystallineFunctor.of iX g h_comm h_p' h_p h_dividedPowers

/-- The open-restriction functor on the relative crystalline categories. -/
abbrev openCrystallineRelativeFunctor :
    RelativeCRIS S' I' γ' h'_compatible X' x₀' ⥤
      RelativeCRIS S I γ h_compatible X x₀ :=
  (openCrystallineFunctor iX I I' γ γ' h_compatible h'_compatible s s'
    x₀ x₀' h_p h_p' g h_comm h_dividedPowers).toRelativeFunctor

/-- Open restriction carries small crystalline objects to small crystalline objects. -/
theorem openCrystallineRelativeFunctor_mapsToSmall :
    Scheme.Crystalline.smallCrystallineProperty S' I' γ' h'_compatible X' x₀' ≤
      (Scheme.Crystalline.smallCrystallineProperty S I γ h_compatible X x₀).inverseImage
        (openCrystallineRelativeFunctor iX I I' γ γ' h_compatible h'_compatible s s'
          x₀ x₀' h_p h_p' g h_comm h_dividedPowers) := sorry

/-- The concrete open-restriction functor between the two small crystalline sites. -/
def openCrystallineSmallFunctor :
    Scheme.Crystalline.smallCrystallineSite S' I' γ' h'_compatible X' x₀' ⥤
      Scheme.Crystalline.smallCrystallineSite S I γ h_compatible X x₀ :=
  ObjectProperty.FullSubcategory.restrict
    (openCrystallineRelativeFunctor iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' g h_comm h_dividedPowers)
    (openCrystallineRelativeFunctor_mapsToSmall iX I I' γ γ' h_compatible
      h'_compatible s s' x₀ x₀' h_p h_p' g h_comm h_dividedPowers)

/-- The source component of a crystalline morphism between restricted objects lifts to `X'`. -/
theorem openCrystallineHomPreimage_source
    {A B : Scheme.Crystalline.smallCrystallineSite S' I' γ' h'_compatible X' x₀'}
    (φ : (openCrystallineSmallFunctor iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' g h_comm h_dividedPowers).obj A ⟶
        (openCrystallineSmallFunctor iX I I' γ γ' h_compatible h'_compatible s s'
          x₀ x₀' h_p h_p' g h_comm h_dividedPowers).obj B) :
    φ.hom.source.left ≫ B.obj.1.source.hom = A.obj.1.source.hom := sorry

/-- The lifted source component satisfies the crystalline inclusion square. -/
theorem openCrystallineHomPreimage_inclusion
    {A B : Scheme.Crystalline.smallCrystallineSite S' I' γ' h'_compatible X' x₀'}
    (φ : (openCrystallineSmallFunctor iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' g h_comm h_dividedPowers).obj A ⟶
        (openCrystallineSmallFunctor iX I I' γ γ' h_compatible h'_compatible s s'
          x₀ x₀' h_p h_p' g h_comm h_dividedPowers).obj B) :
    φ.hom.source.left ≫ B.obj.1.inclusion =
      A.obj.1.inclusion ≫ φ.hom.thickening := sorry

/-- The lifted thickening component commutes with the restricted base map. -/
theorem openCrystallineHomPreimage_base
    {A B : Scheme.Crystalline.smallCrystallineSite S' I' γ' h'_compatible X' x₀'}
    (φ : (openCrystallineSmallFunctor iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' g h_comm h_dividedPowers).obj A ⟶
        (openCrystallineSmallFunctor iX I I' γ γ' h_compatible h'_compatible s s'
          x₀ x₀' h_p h_p' g h_comm h_dividedPowers).obj B) :
    φ.hom.thickening ≫ B.obj.1.thickeningToBase = A.obj.1.thickeningToBase := sorry

/-- The explicit preimage of a morphism under the open-restriction functor. -/
def openCrystallineHomPreimage
    {A B : Scheme.Crystalline.smallCrystallineSite S' I' γ' h'_compatible X' x₀'}
    (φ : (openCrystallineSmallFunctor iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' g h_comm h_dividedPowers).obj A ⟶
        (openCrystallineSmallFunctor iX I I' γ γ' h_compatible h'_compatible s s'
          x₀ x₀' h_p h_p' g h_comm h_dividedPowers).obj B) : A ⟶ B :=
  ObjectProperty.homMk
    { source := Over.homMk φ.hom.source.left
        (openCrystallineHomPreimage_source iX I I' γ γ' h_compatible h'_compatible
          s s' x₀ x₀' h_p h_p' g h_comm h_dividedPowers φ)
      thickening := φ.hom.thickening
      source_comm := openCrystallineHomPreimage_inclusion iX I I' γ γ' h_compatible
        h'_compatible s s' x₀ x₀' h_p h_p' g h_comm h_dividedPowers φ
      base_comm := openCrystallineHomPreimage_base iX I I' γ γ' h_compatible
        h'_compatible s s' x₀ x₀' h_p h_p' g h_comm h_dividedPowers φ
      ideal_compatible := φ.hom.ideal_compatible
      dividedPowers_compatible := φ.hom.dividedPowers_compatible }

/-- Mapping the explicit hom preimage recovers the original crystalline morphism. -/
theorem openCrystallineSmallFunctor_map_preimage
    {A B : Scheme.Crystalline.smallCrystallineSite S' I' γ' h'_compatible X' x₀'}
    (φ : (openCrystallineSmallFunctor iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' g h_comm h_dividedPowers).obj A ⟶
        (openCrystallineSmallFunctor iX I I' γ γ' h_compatible h'_compatible s s'
          x₀ x₀' h_p h_p' g h_comm h_dividedPowers).obj B) :
    (openCrystallineSmallFunctor iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' g h_comm h_dividedPowers).map
        (openCrystallineHomPreimage iX I I' γ γ' h_compatible h'_compatible s s'
          x₀ x₀' h_p h_p' g h_comm h_dividedPowers φ) = φ := sorry

/-- Taking the explicit hom preimage after mapping recovers the original morphism. -/
theorem openCrystallineSmallFunctor_preimage_map
    {A B : Scheme.Crystalline.smallCrystallineSite S' I' γ' h'_compatible X' x₀'}
    (φ : A ⟶ B) :
    openCrystallineHomPreimage iX I I' γ γ' h_compatible h'_compatible s s'
        x₀ x₀' h_p h_p' g h_comm h_dividedPowers
        ((openCrystallineSmallFunctor iX I I' γ γ' h_compatible h'_compatible s s'
          x₀ x₀' h_p h_p' g h_comm h_dividedPowers).map φ) = φ := sorry

end
