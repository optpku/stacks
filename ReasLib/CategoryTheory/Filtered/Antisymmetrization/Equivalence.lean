module

public import ReasLib.CategoryTheory.Filtered.Antisymmetrization.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Thin

/-!
# The categorical equivalence induced by antisymmetrization

This file gives the quotient functor an explicit bundled equivalence whose
inverse uses mathlib's chosen `ofAntisymmetrization` representatives. Its
computation API also covers the opposite equivalence used for inverse systems.
-/

@[expose] public section

open Opposite

universe u v w

noncomputable section

namespace CategoryTheory

variable {I : Type u} [Preorder I]

/-- The functor selecting mathlib's chosen representative of each antisymmetrization class. -/
def ofAntisymmetrizationFunctor (I : Type u) [Preorder I] :
    Antisymmetrization I (· ≤ ·) ⥤ I :=
  (OrderEmbedding.ofAntisymmetrization I).monotone.functor

/-- The chosen-representative functor acts on objects by `ofAntisymmetrization`. -/
@[simp]
theorem ofAntisymmetrizationFunctor.obj
    (a : Antisymmetrization I (· ≤ ·)) :
    (ofAntisymmetrizationFunctor I).obj a = ofAntisymmetrization (· ≤ ·) a := sorry

/-- The chosen-representative functor sends an order morphism to the morphism induced by the
corresponding representative inequality. -/
@[simp]
theorem ofAntisymmetrizationFunctor.map
    {a b : Antisymmetrization I (· ≤ ·)} (f : a ⟶ b) :
    (ofAntisymmetrizationFunctor I).map f =
      homOfLE ((OrderEmbedding.ofAntisymmetrization I).monotone f.le) := sorry

namespace toAntisymmetrizationEquivalence

/-- The unit component compares an index with the chosen representative of its quotient class. -/
def unitApp (I : Type u) [Preorder I] (i : I) :
    i ≅ ofAntisymmetrization (· ≤ ·) (toAntisymmetrization (· ≤ ·) i) :=
  iso_of_both_ways
    (LE.le.hom
      (Antisymmetrization.ofAntisymmetrization_toAntisymmetrization_rel
        (r := (· ≤ ·)) i).2)
    (LE.le.hom
      (Antisymmetrization.ofAntisymmetrization_toAntisymmetrization_rel
        (r := (· ≤ ·)) i).1)

/-- The counit component identifies the quotient of a chosen representative with its class. -/
def counitApp (I : Type u) [Preorder I]
    (a : Antisymmetrization I (· ≤ ·)) :
    toAntisymmetrization (· ≤ ·) (ofAntisymmetrization (· ≤ ·) a) ≅ a :=
  eqToIso (toAntisymmetrization_ofAntisymmetrization (· ≤ ·) a)

/-- The chosen unit components are natural. -/
theorem unitApp.naturality (I : Type u) [Preorder I]
    {i j : I} (f : i ⟶ j) :
    (𝟭 I).map f ≫ (unitApp I j).hom =
      (unitApp I i).hom ≫
        ((toAntisymmetrization_mono.functor :
          I ⥤ Antisymmetrization I (· ≤ ·)) ⋙
            ofAntisymmetrizationFunctor I).map f := sorry

/-- The chosen counit components are natural. -/
theorem counitApp.naturality (I : Type u) [Preorder I]
    {a b : Antisymmetrization I (· ≤ ·)} (f : a ⟶ b) :
    ((ofAntisymmetrizationFunctor I ⋙
      (toAntisymmetrization_mono.functor :
        I ⥤ Antisymmetrization I (· ≤ ·))).map f) ≫ (counitApp I b).hom =
      (counitApp I a).hom ≫ (𝟭 (Antisymmetrization I (· ≤ ·))).map f := sorry

/-- The natural unit built from the mutual-comparability representative specification. -/
def chosenUnitIso (I : Type u) [Preorder I] :
    𝟭 I ≅
      (toAntisymmetrization_mono.functor :
        I ⥤ Antisymmetrization I (· ≤ ·)) ⋙ ofAntisymmetrizationFunctor I :=
  NatIso.ofComponents (unitApp I) (fun f => unitApp.naturality I f)

/-- The natural counit built from the quotient-section specification. -/
def chosenCounitIso (I : Type u) [Preorder I] :
    ofAntisymmetrizationFunctor I ⋙
        (toAntisymmetrization_mono.functor :
          I ⥤ Antisymmetrization I (· ≤ ·)) ≅
      𝟭 (Antisymmetrization I (· ≤ ·)) :=
  NatIso.ofComponents (counitApp I) (fun f => counitApp.naturality I f)

/-- The explicit unit and counit satisfy the forward triangle identity. -/
theorem triangle (I : Type u) [Preorder I] (i : I) :
    (toAntisymmetrization_mono.functor :
        I ⥤ Antisymmetrization I (· ≤ ·)).map ((chosenUnitIso I).hom.app i) ≫
      (chosenCounitIso I).hom.app
        ((toAntisymmetrization_mono.functor :
          I ⥤ Antisymmetrization I (· ≤ ·)).obj i) =
        𝟙 ((toAntisymmetrization_mono.functor :
          I ⥤ Antisymmetrization I (· ≤ ·)).obj i) := sorry

/-- The explicit equivalence from a preorder to its antisymmetrization.

Its inverse selects `ofAntisymmetrization` representatives, rather than the
unspecified object preimages used by the general `Functor.asEquivalence` construction. -/
def _root_.CategoryTheory.toAntisymmetrizationEquivalence
    (I : Type u) [Preorder I] :
    I ≌ Antisymmetrization I (· ≤ ·) where
  functor := toAntisymmetrization_mono.functor
  inverse := ofAntisymmetrizationFunctor I
  unitIso := chosenUnitIso I
  counitIso := chosenCounitIso I
  functor_unitIso_comp := triangle I

end toAntisymmetrizationEquivalence

/-- The forward functor of the explicit equivalence is the quotient functor. -/
@[simp]
theorem toAntisymmetrizationEquivalence.functor (I : Type u) [Preorder I] :
    (toAntisymmetrizationEquivalence I).functor =
      (toAntisymmetrization_mono.functor :
        I ⥤ Antisymmetrization I (· ≤ ·)) := sorry

/-- The forward functor maps an index to its antisymmetrization class. -/
@[simp]
theorem toAntisymmetrizationEquivalence.functor.obj (i : I) :
    (toAntisymmetrizationEquivalence I).functor.obj i =
      toAntisymmetrization (· ≤ ·) i := sorry

/-- The inverse functor of the explicit equivalence is the chosen-representative functor. -/
@[simp]
theorem toAntisymmetrizationEquivalence.inverse (I : Type u) [Preorder I] :
    (toAntisymmetrizationEquivalence I).inverse = ofAntisymmetrizationFunctor I := sorry

/-- The inverse functor selects mathlib's `ofAntisymmetrization` representative. -/
@[simp]
theorem toAntisymmetrizationEquivalence.inverse.obj
    (a : Antisymmetrization I (· ≤ ·)) :
    (toAntisymmetrizationEquivalence I).inverse.obj a =
      ofAntisymmetrization (· ≤ ·) a := sorry

/-- The hom of the unit component is the forward comparison supplied by mutual comparability. -/
@[simp]
theorem toAntisymmetrizationEquivalence.unitIso.hom.app (i : I) :
    (toAntisymmetrizationEquivalence I).unitIso.hom.app i =
      LE.le.hom
        (Antisymmetrization.ofAntisymmetrization_toAntisymmetrization_rel
          (r := (· ≤ ·)) i).2 := sorry

/-- The inverse of the unit component is the reverse comparison supplied by mutual
comparability. -/
@[simp]
theorem toAntisymmetrizationEquivalence.unitIso.inv.app (i : I) :
    (toAntisymmetrizationEquivalence I).unitIso.inv.app i =
      LE.le.hom
        (Antisymmetrization.ofAntisymmetrization_toAntisymmetrization_rel
          (r := (· ≤ ·)) i).1 := sorry

/-- The hom of the counit component is induced by the quotient-section equality. -/
@[simp]
theorem toAntisymmetrizationEquivalence.counitIso.hom.app
    (a : Antisymmetrization I (· ≤ ·)) :
    (toAntisymmetrizationEquivalence I).counitIso.hom.app a =
      eqToHom (toAntisymmetrization_ofAntisymmetrization (· ≤ ·) a) := sorry

/-- The inverse of the counit component is induced by the symmetric quotient-section equality. -/
@[simp]
theorem toAntisymmetrizationEquivalence.counitIso.inv.app
    (a : Antisymmetrization I (· ≤ ·)) :
    (toAntisymmetrizationEquivalence I).counitIso.inv.app a =
      eqToHom (toAntisymmetrization_ofAntisymmetrization (· ≤ ·) a).symm := sorry

/-- On opposite objects, the forward equivalence still applies the quotient projection before
opposition. -/
@[simp]
theorem toAntisymmetrizationEquivalence.op.functor.obj (i : Iᵒᵖ) :
    ((toAntisymmetrizationEquivalence I).op.functor.obj i).unop =
      toAntisymmetrization (· ≤ ·) i.unop := sorry

/-- On opposite objects, the inverse equivalence selects the chosen representative before
opposition. -/
@[simp]
theorem toAntisymmetrizationEquivalence.op.inverse.obj
    (a : (Antisymmetrization I (· ≤ ·))ᵒᵖ) :
    ((toAntisymmetrizationEquivalence I).op.inverse.obj a).unop =
      ofAntisymmetrization (· ≤ ·) a.unop := sorry

variable {C : Type v} [Category.{w} C]

/- Data audit: `ofAntisymmetrizationFunctor` uses mathlib's explicit
`OrderEmbedding.ofAntisymmetrization`, so its inverse object map is exactly
`ofAntisymmetrization`. Any `sorryAx` in the bundled equivalence is confined to
the mutual-comparability component witnesses and the naturality/triangle proof
fields; no carrier or object-map data is chosen by a placeholder. -/

end CategoryTheory
