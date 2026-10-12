/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap60.Definition_60_7_3
import Mathlib.Tactic.CrossRefAttribute

open AlgebraicGeometry CategoryTheory

@[expose] public section

universe u

/-- The explicit data of a crystalline object in the fixed divided-power setup: a source
object `U ⟶ X`, a divided-power thickening `U ⟶ T ⟶ S`, and its compatibility data. -/
structure CrystallineObject (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) where
  /-- The source scheme over `X`. -/
  source : Over X
  /-- The thickening scheme and its structure morphism to `S`. -/
  thickening : Scheme.{u}
  thickeningToBase : thickening ⟶ S
  /-- The closed immersion from the source into the thickening. -/
  inclusion : source.left ⟶ thickening
  /-- The ideal sheaf carrying the divided-power structure on the thickening. -/
  ideal : thickening.IdealSheafData
  gamma : ∀ V : thickening.affineOpens, DividedPowers (ideal.ideal V)
  thickening_compatible :
    ∀ (V : thickening.affineOpens) (f : Γ(thickening, V)),
      (gamma V).IsDPMorphism (gamma (thickening.affineBasicOpen f))
        (thickening.presheaf.map (homOfLE (thickening.basicOpen_le f)).op).hom
  /-- The divided-power ideal defines a scheme-theoretic thickening. -/
  isThickening : IsDividedPowerThickening thickening ideal gamma thickening_compatible
  /-- The stored inclusion itself is a thickening, not merely the canonical
  immersion attached to an unrelated ideal. -/
  inclusion_isThickening : IsThickening inclusion
  /-- The divided-power ideal is exactly the ideal defining the stored inclusion. -/
  ideal_eq_ker : ideal = inclusion.ker
  /-- The structure morphisms commute with the fixed map from the special fibre. -/
  source_comm : inclusion ≫ thickeningToBase = source.hom ≫ x₀ ≫ I.subschemeι

/-- The crystalline compatibility predicate for an object in the fixed setup. -/
def IsCrystallineObject {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : CrystallineObject S I γ h_compatible X x₀) : Prop :=
  IsDividedPowerThickening T.thickening T.ideal T.gamma T.thickening_compatible ∧
    IsThickening T.inclusion ∧ T.ideal = T.inclusion.ker ∧
    (T.inclusion ≫ T.thickeningToBase = T.source.hom ≫ x₀ ≫ I.subschemeι)

/-- A morphism of crystalline objects consists of maps on the source and thickening together with
the square, base, ideal, and divided-power compatibility conditions. -/
structure CrystallineObject.Hom {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (A B : CrystallineObject S I γ h_compatible X x₀) where
  /-- The induced morphism between source objects over `X`. -/
  source : A.source ⟶ B.source
  /-- The induced morphism between the thickening schemes. -/
  thickening : A.thickening ⟶ B.thickening
  source_comm : source.left ≫ B.inclusion = A.inclusion ≫ thickening
  base_comm : thickening ≫ B.thickeningToBase = A.thickeningToBase
  /-- The pullback of the target ideal is contained in the source ideal. -/
  ideal_compatible : B.ideal.comap thickening ≤ A.ideal
  /-- The affine-section maps preserve the divided-power operations. -/
  dividedPowers_compatible :
    ∀ (V : B.thickening.affineOpens) (W : A.thickening.affineOpens)
      (hVW : W.1 ≤ thickening ⁻¹ᵁ V.1),
      (B.gamma V).IsDPMorphism (A.gamma W)
        (thickening.appLE V W hVW).hom

namespace CrystallineObject.Hom

/-- The identity morphism of a crystalline object. -/
def id {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (A : CrystallineObject S I γ h_compatible X x₀) :
    CrystallineObject.Hom A A where
  source := 𝟙 A.source
  thickening := 𝟙 A.thickening
  source_comm := sorry
  base_comm := sorry
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

/-- Composition of morphisms of crystalline objects. -/
def comp {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    {A B C : CrystallineObject S I γ h_compatible X x₀}
    (f : CrystallineObject.Hom A B) (g : CrystallineObject.Hom B C) :
    CrystallineObject.Hom A C where
  source := f.source ≫ g.source
  thickening := f.thickening ≫ g.thickening
  source_comm := sorry
  base_comm := sorry
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

end CrystallineObject.Hom

/-- The CRIS category of crystalline objects in the fixed divided-power setup. -/
abbrev CRIS (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) :=
  CrystallineObject S I γ h_compatible X x₀

instance {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme} :
    Category (CRIS S I γ h_compatible X x₀) where
  Hom := CrystallineObject.Hom
  id := CrystallineObject.Hom.id
  comp := CrystallineObject.Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- A source-facing constructor for crystalline objects from their explicit data and proof fields. -/
noncomputable def CrystallineObject.of {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) (source : Over X)
    (thickening : Scheme.{u}) (thickeningToBase : thickening ⟶ S)
    (inclusion : source.left ⟶ thickening) (ideal : thickening.IdealSheafData)
    (gamma : ∀ V : thickening.affineOpens, DividedPowers (ideal.ideal V))
    (thickening_compatible :
      ∀ (V : thickening.affineOpens) (f : Γ(thickening, V)),
        (gamma V).IsDPMorphism (gamma (thickening.affineBasicOpen f))
          (thickening.presheaf.map (homOfLE (thickening.basicOpen_le f)).op).hom)
    (isThickening : IsDividedPowerThickening thickening ideal gamma thickening_compatible)
    (inclusion_isThickening : IsThickening inclusion)
    (ideal_eq_ker : ideal = inclusion.ker)
    (source_comm : inclusion ≫ thickeningToBase = source.hom ≫ x₀ ≫ I.subschemeι) :
    CrystallineObject S I γ h_compatible X x₀ :=
  { source, thickening, thickeningToBase, inclusion, ideal, gamma, thickening_compatible,
    isThickening, inclusion_isThickening, ideal_eq_ker, source_comm }

/-- The trivial crystalline object has identity thickening and the divided powers on the zero
ideal. -/
noncomputable def trivialCrystallineObject {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) (U : Over X) :
    CRIS S I γ h_compatible X x₀ :=
  { source := U
    thickening := U.left
    thickeningToBase := U.hom ≫ x₀ ≫ I.subschemeι
    inclusion := 𝟙 U.left
    ideal := ⊥
    gamma := fun V => dividedPowersBot _
    thickening_compatible := sorry
    isThickening := sorry
    inclusion_isThickening := sorry
    ideal_eq_ker := sorry
    source_comm := sorry }

end
