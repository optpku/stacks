/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Over
public import ReasLib.RingTheory.Localization.AtPrime.Int
public import stacks_project.Chap60.«60_8_1_2_CrystallineObject»
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/-- The divided-power compatibility of a crystalline object with the fixed setup `(S, I, γ)`. -/
def CrystallineBaseCompatible {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (g : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
          (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (c : CRIS S I γ h_compatible X x₀) : Prop :=
  ∀ (V : S.affineOpens) (W : c.thickening.affineOpens)
    (hVW : W.1 ≤ c.thickeningToBase ⁻¹ᵁ V.1),
    (γ V).IsDPMorphism (c.gamma W) (c.thickeningToBase.appLE V W hVW).hom

/-- The sectionwise characterization of `CrystallineBaseCompatible`. -/
theorem crystallineBaseCompatible_iff {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (g : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
          (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (c : CRIS S I γ h_compatible X x₀) :
    CrystallineBaseCompatible I γ h_compatible x₀ c ↔
      ∀ (V : S.affineOpens) (W : c.thickening.affineOpens)
        (hVW : W.1 ≤ c.thickeningToBase ⁻¹ᵁ V.1),
        (γ V).IsDPMorphism (c.gamma W) (c.thickeningToBase.appLE V W hVW).hom := sorry

/-- The source-faithful crystalline-object category, retaining the divided-power compatibility
with the base setup as an explicit property of each object. -/
abbrev RelativeCRIS (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (g : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
          (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) :=
  { c : CRIS S I γ h_compatible X x₀ // CrystallineBaseCompatible I γ h_compatible x₀ c }

/-- The subtype witness of a `RelativeCRIS` object is its base divided-power compatibility. -/
theorem relativeCRIS_property {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (g : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
          (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (c : RelativeCRIS S I γ h_compatible X x₀) :
    CrystallineBaseCompatible I γ h_compatible x₀ c.1 := sorry

/-- The category structure on `RelativeCRIS` uses the existing crystalline morphisms. -/
instance relativeCRISCategory {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (g : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
          (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme} :
    Category (RelativeCRIS S I γ h_compatible X x₀) where
  Hom := fun A B ↦ A.1 ⟶ B.1
  id := fun A ↦ 𝟙 A.1
  comp := fun f g ↦ f ≫ g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- 60.8.1.1: The forgetful functor from `CRIS(X/S)` to `Sch/X` sends a crystalline
object `(U, T, δ)` to its source object `U` over `X`. -/
@[stacks 07I7]
def crystallineForgetful {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (g : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
          (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    RelativeCRIS S I γ h_compatible X x₀ ⥤ Over X where
  obj := fun c ↦ c.1.source
  map := fun f ↦ CrystallineObject.Hom.source f
  map_id := sorry
  map_comp := sorry

/-- The forgetful functor sends a relative crystalline object to its full source object in `Over X`. -/
@[stacks 07I7]
theorem crystallineForgetful_obj {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (g : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
          (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (c : RelativeCRIS S I γ h_compatible X x₀) :
    (crystallineForgetful S I γ h_compatible s X x₀ h_p).obj c = c.1.source := sorry
