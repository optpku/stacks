/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.SingleObj
import Mathlib.Tactic.CrossRefAttribute

/-!
# Reconstruction of one-object categories

This module identifies any category with a subsingleton object type with the one-object category
of the endomorphism monoid of a chosen object.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory

namespace SingleObj.Reconstruction

/-- A morphism in a category with subsingleton object type, transported to an endomorphism of
the chosen object `c`. -/
def toMap
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C)
    {X Y : C} (f : X ⟶ Y) : End c :=
  eqToHom (Subsingleton.elim c X) ≫ f ≫ eqToHom (Subsingleton.elim Y c)

/-- Transport to the chosen endomorphism monoid preserves identity morphisms. -/
theorem toMap.id
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C) (X : C) :
    toMap c (𝟙 X) = 𝟙 (SingleObj.star (End c)) := sorry

/-- Transport to the chosen endomorphism monoid preserves composition in the one-object
category convention. -/
theorem toMap.comp
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toMap c (f ≫ g) =
      toMap c f ≫ toMap c g := sorry

/-- The explicit inverse to the canonical realization
`SingleObj.functor (MonoidHom.id (End c))`. It sends every object to the unique one-object
category object and transports every morphism to an endomorphism of `c`. -/
def toEnd
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C) :
    C ⥤ SingleObj (End c) where
  obj _ := SingleObj.star (End c)
  map := toMap c
  map_id := toMap.id c
  map_comp := toMap.comp c

/-- The inverse realization sends every object to the unique object of
`SingleObj (End c)`. -/
@[simp]
theorem toEnd.obj
    {C : Type u} [Category.{v} C] [Subsingleton C] (c X : C) :
    (toEnd c).obj X = SingleObj.star (End c) := sorry

/-- The inverse realization maps a morphism by endpoint transport to an endomorphism of `c`. -/
@[simp]
theorem toEnd.map
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C)
    {X Y : C} (f : X ⟶ Y) :
    (toEnd c).map f = toMap c f := sorry

/-- The forward unit component of the one-object realization equivalence is the identity
endomorphism of `c`. -/
def unitHom
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C)
    (X : SingleObj (End c)) :
    X ⟶
      ((SingleObj.functor (MonoidHom.id (End c))) ⋙ toEnd c).obj X :=
  𝟙 c

/-- The inverse unit component of the one-object realization equivalence is the identity
endomorphism of `c`. -/
def unitInv
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C)
    (X : SingleObj (End c)) :
    ((SingleObj.functor (MonoidHom.id (End c))) ⋙ toEnd c).obj X ⟶ X :=
  𝟙 c

/-- The explicit forward and inverse unit components compose to the identity on the source
one-object category object. -/
theorem unitIsoApp.hom_inv
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C)
    (X : SingleObj (End c)) :
    unitHom c X ≫ unitInv c X = 𝟙 X := sorry

/-- The explicit inverse and forward unit components compose to the identity on the reconstructed
one-object category object. -/
theorem unitIsoApp.inv_hom
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C)
    (X : SingleObj (End c)) :
    unitInv c X ≫ unitHom c X =
      𝟙 (((SingleObj.functor (MonoidHom.id (End c))) ⋙ toEnd c).obj X) := sorry

/-- The objectwise unit isomorphism of the explicit one-object realization equivalence. -/
def unitIsoApp
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C)
    (X : SingleObj (End c)) :
    X ≅ ((SingleObj.functor (MonoidHom.id (End c))) ⋙ toEnd c).obj X where
  hom := unitHom c X
  inv := unitInv c X
  hom_inv_id := unitIsoApp.hom_inv c X
  inv_hom_id := unitIsoApp.inv_hom c X

namespace unitIsoApp

/-- The forward unit component is the identity endomorphism of the chosen object. -/
@[simp]
theorem hom
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C)
    (X : SingleObj (End c)) :
    (unitIsoApp c X).hom = 𝟙 c := sorry

/-- The inverse unit component is the identity endomorphism of the chosen object. -/
@[simp]
theorem inv
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C)
    (X : SingleObj (End c)) :
    (unitIsoApp c X).inv = 𝟙 c := sorry

/-- The explicit one-object realization unit components are natural. -/
theorem naturality
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C)
    {X Y : SingleObj (End c)} (f : X ⟶ Y) :
    f ≫ (unitIsoApp c Y).hom =
      (unitIsoApp c X).hom ≫
        ((SingleObj.functor (MonoidHom.id (End c))) ⋙ toEnd c).map f := sorry

end unitIsoApp

/-- The explicit unit natural isomorphism of the one-object realization equivalence. -/
def unitIso
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C) :
    𝟭 (SingleObj (End c)) ≅
      (SingleObj.functor (MonoidHom.id (End c))) ⋙ toEnd c :=
  NatIso.ofComponents
    (unitIsoApp c)
    (fun f ↦ unitIsoApp.naturality c f)

/-- The objectwise counit isomorphism transports the chosen object `c` to each object of the
subsingleton object type. -/
def counitIsoApp
    {C : Type u} [Category.{v} C] [Subsingleton C] (c X : C) :
    (toEnd c ⋙
      SingleObj.functor (MonoidHom.id (End c))).obj X ≅ X :=
  eqToIso (Subsingleton.elim c X)

namespace counitIsoApp

/-- The forward counit component is transport along the unique object equality `c = X`. -/
@[simp]
theorem hom
    {C : Type u} [Category.{v} C] [Subsingleton C] (c X : C) :
    (counitIsoApp c X).hom =
      eqToHom (Subsingleton.elim c X) := sorry

/-- The inverse counit component is transport along the unique object equality `X = c`. -/
@[simp]
theorem inv
    {C : Type u} [Category.{v} C] [Subsingleton C] (c X : C) :
    (counitIsoApp c X).inv =
      eqToHom (Subsingleton.elim X c) := sorry

/-- The explicit one-object realization counit components are natural. -/
theorem naturality
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C)
    {X Y : C} (f : X ⟶ Y) :
    (toEnd c ⋙
        SingleObj.functor (MonoidHom.id (End c))).map f ≫
      (counitIsoApp c Y).hom =
        (counitIsoApp c X).hom ≫ f := sorry

end counitIsoApp

/-- The explicit counit natural isomorphism of the one-object realization equivalence. -/
def counitIso
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C) :
    toEnd c ⋙ SingleObj.functor (MonoidHom.id (End c)) ≅ 𝟭 C :=
  NatIso.ofComponents
    (counitIsoApp c)
    (fun f ↦ counitIsoApp.naturality c f)

/-- Triangle identity for the explicit one-object realization unit and counit. -/
theorem triangle
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C)
    (X : SingleObj (End c)) :
    (SingleObj.functor (MonoidHom.id (End c))).map
        ((unitIso c).hom.app X) ≫
      (counitIso c).hom.app
        ((SingleObj.functor (MonoidHom.id (End c))).obj X) =
      𝟙 ((SingleObj.functor (MonoidHom.id (End c))).obj X) := sorry

/-- A category with subsingleton object type is canonically equivalent to the one-object category
of the endomorphism monoid of any chosen object. -/
@[stacks 0019 "one-object reconstruction by an endomorphism monoid"]
def equivalence
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C) :
    SingleObj (End c) ≌ C :=
  Equivalence.mk'
    (SingleObj.functor (MonoidHom.id (End c)))
    (toEnd c)
    (unitIso c)
    (counitIso c)
    (triangle c)

namespace equivalence

/-- The forward functor of the one-object realization equivalence is mathlib's canonical
`SingleObj.functor`. -/
@[simp]
theorem functor
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C) :
    (equivalence c).functor =
      SingleObj.functor (MonoidHom.id (End c)) := sorry

/-- The inverse functor of the one-object realization equivalence is
`SingleObj.Reconstruction.toEnd c`. -/
@[simp]
theorem inverse
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C) :
    (equivalence c).inverse = toEnd c := sorry

/-- The unit of the one-object realization equivalence is the explicit identity-endomorphism
comparison. -/
@[simp]
theorem unitIso
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C) :
    (equivalence c).unitIso = unitIso c := sorry

/-- The counit of the one-object realization equivalence is the endpoint-transport
comparison. -/
@[simp]
theorem counitIso
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C) :
      (equivalence c).counitIso = counitIso c := sorry

end equivalence

/-- A category whose object type is a subsingleton is equivalent to the one-object category of
the endomorphism monoid of any chosen object. This property bridge is backed by the explicit
data owner `SingleObj.Reconstruction.equivalence`. -/
@[stacks 0019 "one-object reconstruction is an equivalence"]
theorem isEquivalence
    {C : Type u} [Category.{v} C] [Subsingleton C] (c : C) :
    (SingleObj.functor (MonoidHom.id (End c))).IsEquivalence := sorry

end SingleObj.Reconstruction

end CategoryTheory
