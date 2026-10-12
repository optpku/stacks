/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.RingTheory.DividedPowers.Category.Quotient
public import ReasLib.RingTheory.DividedPowers.Thickening

@[expose] public section

open CategoryTheory

universe u v w

namespace DividedPowerThickening

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type v} [CommRing C] (f : A →+* C)
variable (hIC : Ideal.map f I = (⊥ : Ideal C))
variable (h_pC : IsNilpotent (p : C))

/-- The implementation record carrying the data of a thickening morphism. -/
structure HomData
    {hIC : Ideal.map f I = (⊥ : Ideal C)}
    {h_pC : IsNilpotent (p : C)}
    (X Y : DividedPowerThickening p A I γ C f hIC h_pC) where
  map : DividedPowers.DPMorphism X.B.dividedPowers Y.B.dividedPowers
  base_comm : map.toRingHom.comp X.base.toRingHom = Y.base.toRingHom
  quotient_comm : (DividedPowerRing.quotientMap map).comp X.quotient = Y.quotient

/-- A compatible divided-power morphism between two thickenings. -/
def Hom
    {hIC : Ideal.map f I = (⊥ : Ideal C)}
    {h_pC : IsNilpotent (p : C)}
    (X Y : DividedPowerThickening p A I γ C f hIC h_pC) :=
  HomData γ f X Y

namespace Hom

variable {hIC : Ideal.map f I = (⊥ : Ideal C)}
variable {h_pC : IsNilpotent (p : C)}

/-- The underlying divided-power morphism of a thickening morphism. -/
def map {X Y : DividedPowerThickening p A I γ C f hIC h_pC}
    (φ : Hom γ f X Y) : DividedPowers.DPMorphism X.B.dividedPowers Y.B.dividedPowers :=
  HomData.map φ

/-- The base-map compatibility equation of a thickening morphism. -/
def base_comm {X Y : DividedPowerThickening p A I γ C f hIC h_pC} (φ : Hom γ f X Y) :
    φ.map.toRingHom.comp X.base.toRingHom = Y.base.toRingHom :=
  HomData.base_comm φ

/-- The quotient-map compatibility equation of a thickening morphism. -/
def quotient_comm {X Y : DividedPowerThickening p A I γ C f hIC h_pC} (φ : Hom γ f X Y) :
    (DividedPowerRing.quotientMap φ.map).comp X.quotient = Y.quotient :=
  HomData.quotient_comm φ

/-- Construct a thickening morphism from its map and compatibility equations. -/
def of {X Y : DividedPowerThickening p A I γ C f hIC h_pC}
    (map : DividedPowers.DPMorphism X.B.dividedPowers Y.B.dividedPowers)
    (base_comm : map.toRingHom.comp X.base.toRingHom = Y.base.toRingHom)
    (quotient_comm : (DividedPowerRing.quotientMap map).comp X.quotient = Y.quotient) :
    Hom γ f X Y :=
  HomData.mk map base_comm quotient_comm

/-- The defining compatibility equations for a thickening morphism. -/
theorem spec {X Y : DividedPowerThickening p A I γ C f hIC h_pC} (φ : Hom γ f X Y) :
    φ.map.toRingHom.comp X.base.toRingHom = Y.base.toRingHom ∧
      (DividedPowerRing.quotientMap φ.map).comp X.quotient = Y.quotient := sorry

/-- Extensionality for thickening morphisms. -/
theorem ext {X Y : DividedPowerThickening p A I γ C f hIC h_pC}
    {φ ψ : Hom γ f X Y} (h : φ.map = ψ.map) : φ = ψ := sorry

/-- The base compatibility equation for the identity thickening morphism. -/
theorem id_base_comm (X : DividedPowerThickening p A I γ C f hIC h_pC) :
    (DividedPowers.DPMorphism.id X.B.dividedPowers).toRingHom.comp X.base.toRingHom = X.base.toRingHom := sorry

/-- The quotient compatibility equation for the identity thickening morphism. -/
theorem id_quotient_comm (X : DividedPowerThickening p A I γ C f hIC h_pC) :
    (DividedPowerRing.quotientMap (DividedPowers.DPMorphism.id X.B.dividedPowers)).comp X.quotient = X.quotient := sorry

/-- The identity morphism of a divided-power thickening. -/
def id (X : DividedPowerThickening p A I γ C f hIC h_pC) : Hom γ f X X :=
  Hom.of (γ := γ) (f := f) (DividedPowers.DPMorphism.id X.B.dividedPowers)
    (id_base_comm (γ := γ) (f := f) (hIC := hIC) (h_pC := h_pC) X)
    (id_quotient_comm (γ := γ) (f := f) (hIC := hIC) (h_pC := h_pC) X)

/-- The base compatibility equation for a composite thickening morphism. -/
theorem comp_base_comm {X Y Z : DividedPowerThickening p A I γ C f hIC h_pC}
    (φ : Hom γ f X Y) (ψ : Hom γ f Y Z) :
    (DividedPowers.DPMorphism.comp ψ.map φ.map).toRingHom.comp X.base.toRingHom = Z.base.toRingHom := sorry

/-- The quotient compatibility equation for a composite thickening morphism. -/
theorem comp_quotient_comm {X Y Z : DividedPowerThickening p A I γ C f hIC h_pC}
    (φ : Hom γ f X Y) (ψ : Hom γ f Y Z) :
    (DividedPowerRing.quotientMap (DividedPowers.DPMorphism.comp ψ.map φ.map)).comp X.quotient = Z.quotient := sorry

/-- Composition of homomorphisms of divided-power thickenings. -/
def comp {X Y Z : DividedPowerThickening p A I γ C f hIC h_pC}
    (φ : Hom γ f X Y) (ψ : Hom γ f Y Z) : Hom γ f X Z :=
  Hom.of (γ := γ) (f := f) (DividedPowers.DPMorphism.comp ψ.map φ.map)
    (comp_base_comm (γ := γ) (f := f) (hIC := hIC) (h_pC := h_pC) φ ψ)
    (comp_quotient_comm (γ := γ) (f := f) (hIC := hIC) (h_pC := h_pC) φ ψ)

/-- The left identity law for thickening morphisms. -/
theorem id_comp {X Y : DividedPowerThickening p A I γ C f hIC h_pC} (φ : Hom γ f X Y) :
    comp γ f (id γ f X) φ = φ := sorry

/-- The right identity law for thickening morphisms. -/
theorem comp_id {X Y : DividedPowerThickening p A I γ C f hIC h_pC} (φ : Hom γ f X Y) :
    comp γ f φ (id γ f Y) = φ := sorry

/-- The associativity law for thickening morphisms. -/
theorem assoc {W X Y Z : DividedPowerThickening p A I γ C f hIC h_pC}
    (φ : Hom γ f W X) (ψ : Hom γ f X Y) (χ : Hom γ f Y Z) :
    comp γ f (comp γ f φ ψ) χ = comp γ f φ (comp γ f ψ χ) := sorry

end Hom

/-- The category of affine divided-power thickenings in the fixed setup. -/
abbrev CRIS := DividedPowerThickening p A I γ C f hIC h_pC

/-- The category structure on affine divided-power thickenings. -/
instance crisCategory : Category (CRIS γ f hIC h_pC) where
  Hom := Hom γ f
  id := Hom.id γ f
  comp := fun φ ψ ↦ Hom.comp γ f φ ψ
  id_comp := Hom.id_comp γ f
  comp_id := Hom.comp_id γ f
  assoc := Hom.assoc γ f

/-- The object property selecting thickenings with invertible quotient map. -/
def isCrisObject : ObjectProperty (CRIS γ f hIC h_pC) :=
  fun T ↦ IsIso (CommRingCat.ofHom T.quotient)

/-- The quotient-map characterization of the crystalline object property. -/
theorem isCrisObject_iff (T : CRIS γ f hIC h_pC) :
    isCrisObject γ f hIC h_pC T ↔ IsIso (CommRingCat.ofHom T.quotient) := sorry

/-- The full subcategory of `CRIS` on thickenings with invertible quotient map. -/
abbrev Cris := (isCrisObject γ f hIC h_pC).FullSubcategory

/-- Membership in the full subcategory of crystalline thickenings. -/
theorem cris_mem (T : Cris γ f hIC h_pC) :
    isCrisObject γ f hIC h_pC T.obj := sorry

namespace Cris

/-- The quotient map of a crystalline thickening is an isomorphism. -/
instance quotient_isIso (T : Cris γ f hIC h_pC) : IsIso (CommRingCat.ofHom T.obj.quotient) := T.property

/-- The map from the thickening ring to the base algebra induced by the quotient isomorphism. -/
noncomputable def toC (T : Cris γ f hIC h_pC) : T.obj.B →+* C :=
  (inv (CommRingCat.ofHom T.obj.quotient)).hom.comp (Ideal.Quotient.mk T.obj.B.ideal)

/-- The induced map to `C` followed by the quotient map is the quotient projection. -/
theorem toC_comp_quotient (T : Cris γ f hIC h_pC) :
    T.obj.quotient.comp T.toC = Ideal.Quotient.mk T.obj.B.ideal := sorry

/-- The quotient map followed by the induced map to `C` is the identity on `C`. -/
theorem quotient_comp_toC (T : Cris γ f hIC h_pC) :
    (inv (CommRingCat.ofHom T.obj.quotient)).hom.comp T.obj.quotient = RingHom.id C := sorry

/-- The kernel of the induced map to `C` is the distinguished ideal. -/
theorem ker_toC (T : Cris γ f hIC h_pC) :
    RingHom.ker T.toC = T.obj.B.ideal := sorry

/-- The induced map from the thickening ring to `C` is surjective. -/
theorem toC_surjective (T : Cris γ f hIC h_pC) : Function.Surjective T.toC := sorry

end Cris

end DividedPowerThickening
