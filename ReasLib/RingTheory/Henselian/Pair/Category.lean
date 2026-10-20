module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.CrossRefAttribute

/-!
# The category of Henselian pairs

Commutative-ring pairs `(A, I)` form a category via their quotient arrows. Henselian pairs
form a full subcategory, and a left adjoint to its inclusion supplies Henselization objects,
their underlying rings and ideals, and natural unit maps.
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

/-- A commutative ring equipped with a distinguished ideal. -/
@[stacks 0A02 "category of ring pairs"]
def RingPairCat : Type (u + 1) :=
  Σ R : CommRingCat.{u}, Ideal R

namespace RingPairCat

/-- The underlying commutative ring of a ring pair. -/
abbrev ring (X : RingPairCat.{u}) : CommRingCat.{u} := X.1

/-- The distinguished ideal of a ring pair. -/
def ideal (X : RingPairCat.{u}) : Ideal X.ring := X.2

/-- Pair a commutative ring with a distinguished ideal. -/
abbrev mk (ring : CommRingCat.{u}) (ideal : Ideal ring) : RingPairCat.{u} :=
  ⟨ring, ideal⟩

/-- The quotient arrow `A ⟶ A ⧸ I` attached to a ring pair `(A, I)`. -/
@[stacks 0A02 "quotient arrow of a ring pair"]
def quotientArrow (X : RingPairCat.{u}) : Arrow CommRingCat.{u} :=
  Arrow.mk
    (show X.ring ⟶ CommRingCat.of (X.ring ⧸ X.ideal) from
      CommRingCat.ofHom (Ideal.Quotient.mk X.ideal))

/-- Morphisms of ring pairs are the morphisms induced from their quotient arrows. -/
@[stacks 0A02 "category structure on ring pairs", instance]
instance : Category RingPairCat.{u} :=
  inferInstanceAs (Category (InducedCategory (Arrow CommRingCat.{u}) quotientArrow))

/-- The underlying ring homomorphism of a morphism of ring pairs. -/
@[stacks 0A02 "underlying ring homomorphism of a pair morphism"]
abbrev ringHom {X Y : RingPairCat.{u}} (f : X ⟶ Y) : X.ring →+* Y.ring :=
  f.hom.left.hom

/-- The object property defining Henselian pairs. -/
@[stacks 0A02 "Henselian-pair object property"]
def henselianPairProperty : ObjectProperty RingPairCat.{u} :=
  fun X ↦ HenselianRing X.ring X.ideal

/-- The full subcategory of Henselian ring pairs. -/
@[stacks 0A02 "category of Henselian pairs"]
abbrev HenselianPairCat := henselianPairProperty.FullSubcategory

/-- The inclusion of Henselian pairs into all ring pairs. -/
@[stacks 0A02 "inclusion of Henselian pairs"]
abbrev henselianPairInclusion : HenselianPairCat.{u} ⥤ RingPairCat.{u} :=
  henselianPairProperty.ι

/-- The inclusion of Henselian pairs into ring pairs is a right adjoint. -/
@[stacks 0A02 "Lemma 15.12.1", instance]
theorem henselianPairInclusion_isRightAdjoint :
    henselianPairInclusion.IsRightAdjoint := sorry

/-- The chosen Henselization of a ring pair supplied by the left adjoint. -/
@[stacks 0A02 "chosen Henselization of a pair"]
abbrev henselization (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint] :
    HenselianPairCat.{u} :=
  henselianPairInclusion.leftAdjoint.obj X

/-- The underlying ring pair of the chosen Henselization. -/
@[stacks 0A02 "underlying pair of the chosen Henselization"]
abbrev henselizationPair (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint] :
    RingPairCat.{u} :=
  henselianPairInclusion.obj (henselization X)

/-- The underlying commutative ring of the chosen Henselization. -/
@[stacks 0A02 "Henselization ring"]
abbrev henselizationRing (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint] :
    CommRingCat.{u} :=
  (henselizationPair X).ring

/-- The distinguished ideal of the chosen Henselization. -/
@[stacks 0A02 "Henselization ideal"]
abbrev henselizationIdeal (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint] :
    Ideal (henselizationRing X) :=
  (henselizationPair X).ideal

/-- The canonical ring map from a pair to its chosen Henselization. -/
@[stacks 0A02 "unit map to pair Henselization"]
abbrev toHenselization (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint] :
    X.ring →+* henselizationRing X :=
  ((Adjunction.ofIsRightAdjoint henselianPairInclusion).unit.app X).hom.left.hom

/-- The map between chosen Henselization objects induced by a morphism of pairs. -/
@[stacks 0A02 "functorial map on chosen Henselization objects"]
abbrev henselizationMap {X Y : RingPairCat.{u}} (f : X ⟶ Y)
    [henselianPairInclusion.IsRightAdjoint] :
    henselization X ⟶ henselization Y :=
  henselianPairInclusion.leftAdjoint.map f

/-- The underlying ring map between chosen Henselizations induced by a morphism of pairs. -/
@[stacks 0A02 "functorial map on Henselization rings"]
abbrev henselizationRingMap {X Y : RingPairCat.{u}} (f : X ⟶ Y)
    [henselianPairInclusion.IsRightAdjoint] :
    henselizationRing X →+* henselizationRing Y :=
  ringHom <| henselianPairInclusion.map (henselizationMap f)

/-- Naturality of the unit map to pair Henselization on underlying rings. -/
theorem toHenselization_naturality {X Y : RingPairCat.{u}} (f : X ⟶ Y)
    [henselianPairInclusion.IsRightAdjoint] :
    (toHenselization Y).comp (ringHom f) =
      (henselizationRingMap f).comp (toHenselization X) := sorry

/-- The chosen Henselization ring carries its canonical algebra structure over the source ring. -/
@[stacks 0A02 "algebra structure on the chosen Henselization ring", instance]
instance henselizationRing_algebra (X : RingPairCat.{u})
    [henselianPairInclusion.IsRightAdjoint] :
    Algebra X.ring (henselizationRing X) :=
  (toHenselization X).toAlgebra

/-- The ring pair attached to an ideal of a commutative ring. -/
@[stacks 0A02 "ring pair attached to an ideal"]
abbrev pairOfIdeal {A : Type u} [CommRing A] (I : Ideal A) : RingPairCat.{u} :=
  RingPairCat.mk (CommRingCat.of A) I

/-- A chosen Henselization of `(A, I)` carries its canonical `A`-algebra structure. -/
@[stacks 0A02 "algebra structure on the Henselization of an ideal pair", instance]
instance pairOfIdeal_henselizationRing_algebra {A : Type u} [CommRing A] (I : Ideal A)
    [henselianPairInclusion.IsRightAdjoint] :
    Algebra A (henselizationRing (pairOfIdeal I)) :=
  (toHenselization (pairOfIdeal I)).toAlgebra

section PairMap

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A) (J : Ideal B)

/-- The quotient square attached to an algebra map carrying `I` into `J` commutes. -/
theorem pairOfIdeal_hom_square (hIJ : I ≤ Ideal.comap (algebraMap A B) J) :
    CommRingCat.ofHom (algebraMap A B) ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) =
      CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
        CommRingCat.ofHom (Ideal.quotientMap J (algebraMap A B) hIJ) := sorry

/-- The quotient square attached to a ring homomorphism carrying `I` into `J` commutes. -/
theorem pairOfIdeal_hom_square_of_ringHom {A B : Type u} [CommRing A] [CommRing B]
    (I : Ideal A) (J : Ideal B) (f : A →+* B) (hIJ : I ≤ Ideal.comap f J) :
    CommRingCat.ofHom f ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) =
      CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
        CommRingCat.ofHom (Ideal.quotientMap J f hIJ) := sorry

/-- The morphism of ring pairs induced by an algebra map carrying `I` into `J`. -/
@[stacks 0A02 "morphism between ideal pairs"]
abbrev pairOfIdealMap (hIJ : I ≤ Ideal.comap (algebraMap A B) J) :
    pairOfIdeal I ⟶ pairOfIdeal J :=
  InducedCategory.homMk <|
    Arrow.homMk'
      (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (Ideal.quotientMap J (algebraMap A B) hIJ))
      (by
        ext x
        rfl)

end PairMap

/-- A morphism of ring pairs is determined by its underlying ring homomorphism. -/
theorem hom_ext {X Y : RingPairCat.{u}} {f g : X ⟶ Y}
    (hfg : ringHom f = ringHom g) :
    f = g := sorry

/-- A morphism of ring pairs carries the distinguished source ideal into the target ideal. -/
theorem ringHom_ideal_le_comap {X Y : RingPairCat.{u}} (f : X ⟶ Y) :
    X.ideal ≤ Ideal.comap (ringHom f) Y.ideal := sorry

/-- Explicit universal-arrow data exhibiting a Henselian pair over `X`. -/
@[stacks 0A02 "universal Henselian pair"]
structure PairHenselizationData (X : RingPairCat.{u}) where
  obj : HenselianPairCat.{u}
  unit : X ⟶ henselianPairInclusion.obj obj
  universal :
    ∀ Z : HenselianPairCat.{u},
      Function.Bijective fun f : obj ⟶ Z ↦ unit ≫ henselianPairInclusion.map f

namespace PairHenselizationData

/-- Composition with the universal unit maps a Henselian-pair morphism to a morphism over
the original ring pair. -/
def comparisonMap {X : RingPairCat.{u}} (D : PairHenselizationData X)
    (Z : HenselianPairCat.{u}) :
    (D.obj ⟶ Z) → (X ⟶ henselianPairInclusion.obj Z) :=
  fun f ↦ D.unit ≫ henselianPairInclusion.map f

/-- Composition with the universal unit is a bijection on morphisms to every Henselian pair. -/
theorem comparisonMap_bijective {X : RingPairCat.{u}} (D : PairHenselizationData X)
    (Z : HenselianPairCat.{u}) : Function.Bijective (D.comparisonMap Z) :=
  D.universal Z

end PairHenselizationData

end RingPairCat
