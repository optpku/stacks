/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.Scheme.DividedPowerThickening
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.RingTheory.Localization.AtPrime.Int

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

/-- A crystalline object satisfies its thickening, defining-ideal, and structural-square conditions. -/
theorem CrystallineObject.spec {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : CrystallineObject S I γ h_compatible X x₀) : IsCrystallineObject T :=
  ⟨T.isThickening, T.inclusion_isThickening, T.ideal_eq_ker, T.source_comm⟩

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

/-- A crystalline morphism commutes with source inclusions and base maps and preserves
both the defining ideals and their divided-power operations. -/
theorem CrystallineObject.Hom.spec {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (A B : CrystallineObject S I γ h_compatible X x₀)
    (f : CrystallineObject.Hom A B) :
    (f.source.left ≫ B.inclusion = A.inclusion ≫ f.thickening) ∧
    (f.thickening ≫ B.thickeningToBase = A.thickeningToBase) ∧
    (B.ideal.comap f.thickening ≤ A.ideal) ∧
    (∀ (V : B.thickening.affineOpens) (W : A.thickening.affineOpens)
      (hVW : W.1 ≤ f.thickening ⁻¹ᵁ V.1),
      (B.gamma V).IsDPMorphism (A.gamma W) (f.thickening.appLE V W hVW).hom) :=
  ⟨f.source_comm, f.base_comm, f.ideal_compatible, f.dividedPowers_compatible⟩

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
def CRIS (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) : Cat.{u, u + 1} :=
  @Cat.of.{u, u + 1} (CrystallineObject S I γ h_compatible X x₀)
    { Hom := fun (A B : CrystallineObject S I γ h_compatible X x₀) => CrystallineObject.Hom A B
      id := CrystallineObject.Hom.id
      comp := fun {A B C} f g => CrystallineObject.Hom.comp (A := A) (B := B) (C := C) f g
      id_comp := sorry
      comp_id := sorry
      assoc := sorry }

/-- Construct a crystalline object from its source, thickening, divided powers, and compatibility laws. -/
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
        (γ V).IsDPMorphism (c.gamma W) (c.thickeningToBase.appLE V W hVW).hom := Iff.rfl

/-- The category of crystalline objects whose structure maps preserve the base divided powers. -/
def RelativeCRIS (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (g : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
          (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) : Cat.{u, u + 1} :=
  @Cat.of.{u, u + 1} { c : CRIS S I γ h_compatible X x₀ //
      CrystallineBaseCompatible I γ h_compatible x₀ c }
    { Hom := fun A B => CrystallineObject.Hom A.1 B.1
      id := fun A => CrystallineObject.Hom.id A.1
      comp := fun {A B C} f g => CrystallineObject.Hom.comp (A := A.1) (B := B.1) (C := C.1) f g
      id_comp := fun {A B} f => @Category.id_comp _ (Cat.str (CRIS S I γ h_compatible X x₀)) A.1 B.1 f
      comp_id := fun {A B} f => @Category.comp_id _ (Cat.str (CRIS S I γ h_compatible X x₀)) A.1 B.1 f
      assoc := fun {A B C D} f g h => @Category.assoc _ (Cat.str (CRIS S I γ h_compatible X x₀)) A.1 B.1 C.1 D.1 f g h }

/-- The subtype witness of a `RelativeCRIS` object is its base divided-power compatibility. -/
theorem relativeCRIS_property {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (g : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
          (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (c : RelativeCRIS S I γ h_compatible X x₀) :
    CrystallineBaseCompatible I γ h_compatible x₀ c.1 := c.2

/-- The forgetful functor from relative crystalline objects to schemes over `X` sends a crystalline
object `(U, T, δ)` to its source object `U` over `X`. -/
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
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- The forgetful functor sends a relative crystalline object to its full source object in `Over X`. -/
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
    (crystallineForgetful S I γ h_compatible s X x₀ h_p).obj c = c.1.source := rfl


variable {S : Scheme.{u}} {I : S.IdealSheafData}
  {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
  {h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
  {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- Restrict a crystalline thickening to an open of its thickening scheme. -/
noncomputable def CrystallineObject.restrictOpen
    (T : CRIS S I γ h_compatible X x₀) (U : T.thickening.Opens) :
    CRIS S I γ h_compatible X x₀ where
  source := Over.mk ((T.inclusion ⁻¹ᵁ U).ι ≫ T.source.hom)
  thickening := U.toScheme
  thickeningToBase := U.ι ≫ T.thickeningToBase
  inclusion := T.inclusion ∣_ U
  ideal := (T.inclusion ∣_ U).ker
  gamma W := DividedPowers.ofRingEquiv
    (e := (U.ι.appIso W.1).commRingCatIsoToRingEquiv) sorry
    (T.gamma ⟨U.ι ''ᵁ W.1, W.2.image_of_isOpenImmersion _⟩)
  thickening_compatible := sorry
  isThickening := sorry
  inclusion_isThickening := sorry
  ideal_eq_ker := rfl
  source_comm := sorry

/-- Inclusion of opens induces a morphism of restricted crystalline thickenings. -/
noncomputable def CrystallineObject.restrictOpenHom
    (T : CRIS S I γ h_compatible X x₀) {U V : T.thickening.Opens} (h : U ≤ V) :
    CrystallineObject.Hom (CrystallineObject.restrictOpen T U) (CrystallineObject.restrictOpen T V) where
  source := Over.homMk (T.source.left.homOfLE ((TopologicalSpace.Opens.map T.inclusion.base).monotone h)) sorry
  thickening := T.thickening.homOfLE h
  source_comm := sorry
  base_comm := sorry
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

/-- A crystalline morphism restricts over every open of its target thickening. -/
noncomputable def CrystallineObject.Hom.restrictOpen
    {A B : CRIS S I γ h_compatible X x₀} (f : CrystallineObject.Hom A B)
    (U : B.thickening.Opens) :
    CrystallineObject.Hom (CrystallineObject.restrictOpen A (f.thickening ⁻¹ᵁ U)) (CrystallineObject.restrictOpen B U) where
  source := Over.homMk
    (A.source.left.homOfLE sorry ≫
      (f.source.left ∣_ (B.inclusion ⁻¹ᵁ U))) sorry
  thickening := f.thickening ∣_ U
  source_comm := sorry
  base_comm := sorry
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

/-- Open restriction preserves compatibility with the base divided powers. -/
noncomputable def AlgebraicGeometry.Scheme.Crystalline.relativeRestrictOpen
    (T : RelativeCRIS S I γ h_compatible X x₀) (U : T.1.thickening.Opens) :
    RelativeCRIS S I γ h_compatible X x₀ :=
  ⟨CrystallineObject.restrictOpen T.1 U, sorry⟩

end
