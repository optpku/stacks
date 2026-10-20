/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Constructions.Adjunction.Mapping

/-!
# Pseudofunctorial action on bicategorical adjunctions

Assembly and computation rules for the pseudofunctor induced on bicategories
of adjunctions.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory
namespace Pseudofunctor

universe wC vC uC wD vD uD

variable {B : Type u} [Bicategory.{w, v} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

section MapAdjunctionsImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The implementation-level prelax action of a pseudofunctor on adjunctions and mate
transformations. -/
private def mapAdj.prelax (F : B ⥤ᵖ C) :
    PrelaxFunctor (Bicategory.Adj B) (Bicategory.Adj C) :=
  PrelaxFunctor.mkOfHomFunctors
    (mapAdj.object F) (mapAdj.hom.functor F)

/-- The induced action on adjunctions preserves left whiskering. -/
private theorem mapAdj.map₂.whiskerLeft (F : B ⥤ᵖ C) :
    ∀ {a b c : Bicategory.Adj B}
      (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h),
      (mapAdj.prelax F).map₂ (f ◁ η) =
        (mapAdj.mapCompIso F f g).hom ≫
          (mapAdj.prelax F).map f ◁
            (mapAdj.prelax F).map₂ η ≫
          (mapAdj.mapCompIso F f h).inv := sorry

/-- The induced action on adjunctions preserves right whiskering. -/
private theorem mapAdj.map₂.whiskerRight (F : B ⥤ᵖ C) :
    ∀ {a b c : Bicategory.Adj B}
      {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c),
      (mapAdj.prelax F).map₂ (η ▷ h) =
        (mapAdj.mapCompIso F f h).hom ≫
          (mapAdj.prelax F).map₂ η ▷
            (mapAdj.prelax F).map h ≫
          (mapAdj.mapCompIso F g h).inv := sorry

/-- The induced action on adjunctions preserves the associator modulo its canonical
composition comparisons. -/
private theorem mapAdj.map₂.associator (F : B ⥤ᵖ C) :
    ∀ {a b c d : Bicategory.Adj B}
      (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      (mapAdj.prelax F).map₂ (α_ f g h).hom =
        (mapAdj.mapCompIso F (f ≫ g) h).hom ≫
          (mapAdj.mapCompIso F f g).hom ▷
            (mapAdj.prelax F).map h ≫
          (α_ ((mapAdj.prelax F).map f)
            ((mapAdj.prelax F).map g)
            ((mapAdj.prelax F).map h)).hom ≫
          (mapAdj.prelax F).map f ◁
            (mapAdj.mapCompIso F g h).inv ≫
          (mapAdj.mapCompIso F f (g ≫ h)).inv := sorry

/-- The induced action on adjunctions preserves the left unitor modulo its canonical identity
and composition comparisons. -/
private theorem mapAdj.map₂.leftUnitor (F : B ⥤ᵖ C) :
    ∀ {a b : Bicategory.Adj B} (f : a ⟶ b),
      (mapAdj.prelax F).map₂ (λ_ f).hom =
        (mapAdj.mapCompIso F (𝟙 a) f).hom ≫
          (mapAdj.mapIdIso F a).hom ▷
            (mapAdj.prelax F).map f ≫
          (λ_ ((mapAdj.prelax F).map f)).hom := sorry

/-- The induced action on adjunctions preserves the right unitor modulo its canonical identity
and composition comparisons. -/
private theorem mapAdj.map₂.rightUnitor (F : B ⥤ᵖ C) :
    ∀ {a b : Bicategory.Adj B} (f : a ⟶ b),
      (mapAdj.prelax F).map₂ (ρ_ f).hom =
        (mapAdj.mapCompIso F f (𝟙 b)).hom ≫
          (mapAdj.prelax F).map f ◁
            (mapAdj.mapIdIso F b).hom ≫
          (ρ_ ((mapAdj.prelax F).map f)).hom := sorry

end Implementation

/-- The pseudofunctor induced on bicategories of adjunctions.

It sends an adjunction to its canonical image under `F` and sends a mate transformation by
mapping both mate components. Its identity and composition comparisons are the mate pairs
formed from `F.mapId` and `F.mapComp`. -/
@[stacks 0040 "pseudofunctorial action on bicategorical adjunctions"]
def mapAdj (F : B ⥤ᵖ C) :
    Bicategory.Adj B ⥤ᵖ Bicategory.Adj C where
  toPrelaxFunctor := Implementation.mapAdj.prelax F
  mapId := mapAdj.mapIdIso F
  mapComp := mapAdj.mapCompIso F
  map₂_whisker_left := Implementation.mapAdj.map₂.whiskerLeft F
  map₂_whisker_right := Implementation.mapAdj.map₂.whiskerRight F
  map₂_associator := Implementation.mapAdj.map₂.associator F
  map₂_left_unitor := Implementation.mapAdj.map₂.leftUnitor F
  map₂_right_unitor := Implementation.mapAdj.map₂.rightUnitor F

/-- The object action of the induced pseudofunctor on adjunctions. -/
@[simp]
theorem mapAdj.obj
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    F.mapAdj.obj a = mapAdj.object F a := sorry

/-- The ambient object underlying the image of an object of `Adj B`. -/
@[simp]
theorem mapAdj.obj.carrier
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    (F.mapAdj.obj a).obj = F.obj a.obj := sorry

/-- The `1`-morphism action of the induced pseudofunctor on adjunctions. -/
@[simp]
theorem mapAdj.map
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    F.mapAdj.map f = mapAdj.hom F f := sorry

/-- The left adjoint underlying the image of an adjunction. -/
@[simp]
theorem mapAdj.map.l
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (F.mapAdj.map f).l = F.map f.l := sorry

/-- The right adjoint underlying the image of an adjunction. -/
@[simp]
theorem mapAdj.map.r
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (F.mapAdj.map f).r = F.map f.r := sorry

/-- The adjunction underlying the image of an `Adj`-morphism. -/
@[simp]
theorem mapAdj.map.adj
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (F.mapAdj.map f).adj =
      F.mapAdjunction f.adj := sorry

/-- The `2`-morphism action of the induced pseudofunctor on mate transformations. -/
@[simp]
theorem mapAdj.map₂
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    {f g : a ⟶ b} (η : f ⟶ g) :
    F.mapAdj.map₂ η = mapAdj.hom₂ F η := sorry

/-- The left-adjoint component of the image of a mate transformation. -/
@[simp]
theorem mapAdj.map₂.τl
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    {f g : a ⟶ b} (η : f ⟶ g) :
    (F.mapAdj.map₂ η).τl = F.map₂ η.τl := sorry

/-- The right-adjoint component of the image of a mate transformation. -/
@[simp]
theorem mapAdj.map₂.τr
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    {f g : a ⟶ b} (η : f ⟶ g) :
    (F.mapAdj.map₂ η).τr = F.map₂ η.τr := sorry

/-- The hom-category action of the induced pseudofunctor is the canonical mate-mapping
functor. -/
@[simp]
theorem mapAdj.mapFunctor
    (F : B ⥤ᵖ C) (a b : Bicategory.Adj B) :
    F.mapAdj.mapFunctor a b =
      mapAdj.hom.functor F a b := sorry

/-- The identity comparison of the induced pseudofunctor on adjunctions. -/
@[simp]
theorem mapAdj.mapId
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    F.mapAdj.mapId a = mapAdj.mapIdIso F a := sorry

/-- The forward left-adjoint component of the induced identity comparison. -/
@[simp]
theorem mapAdj.mapId.hom.τl
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    (F.mapAdj.mapId a).hom.τl =
      (F.mapId a.obj).hom := sorry

/-- The forward right-adjoint component of the induced identity comparison. -/
@[simp]
theorem mapAdj.mapId.hom.τr
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    (F.mapAdj.mapId a).hom.τr =
      (F.mapId a.obj).inv := sorry

/-- The inverse left-adjoint component of the induced identity comparison. -/
@[simp]
theorem mapAdj.mapId.inv.τl
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    (F.mapAdj.mapId a).inv.τl =
      (F.mapId a.obj).inv := sorry

/-- The inverse right-adjoint component of the induced identity comparison. -/
@[simp]
theorem mapAdj.mapId.inv.τr
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    (F.mapAdj.mapId a).inv.τr =
      (F.mapId a.obj).hom := sorry

/-- The composition comparison of the induced pseudofunctor on adjunctions. -/
@[simp]
theorem mapAdj.mapComp
    (F : B ⥤ᵖ C) {a b c : Bicategory.Adj B}
    (f : a ⟶ b) (g : b ⟶ c) :
    F.mapAdj.mapComp f g =
      mapAdj.mapCompIso F f g := sorry

/-- The forward left-adjoint component of the induced composition comparison. -/
@[simp]
theorem mapAdj.mapComp.hom.τl
    (F : B ⥤ᵖ C) {a b c : Bicategory.Adj B}
    (f : a ⟶ b) (g : b ⟶ c) :
    (F.mapAdj.mapComp f g).hom.τl =
      (F.mapComp f.l g.l).hom := sorry

/-- The forward right-adjoint component of the induced composition comparison. -/
@[simp]
theorem mapAdj.mapComp.hom.τr
    (F : B ⥤ᵖ C) {a b c : Bicategory.Adj B}
    (f : a ⟶ b) (g : b ⟶ c) :
    (F.mapAdj.mapComp f g).hom.τr =
      (F.mapComp g.r f.r).inv := sorry

/-- The inverse left-adjoint component of the induced composition comparison. -/
@[simp]
theorem mapAdj.mapComp.inv.τl
    (F : B ⥤ᵖ C) {a b c : Bicategory.Adj B}
    (f : a ⟶ b) (g : b ⟶ c) :
    (F.mapAdj.mapComp f g).inv.τl =
      (F.mapComp f.l g.l).inv := sorry

/-- The inverse right-adjoint component of the induced composition comparison. -/
@[simp]
theorem mapAdj.mapComp.inv.τr
    (F : B ⥤ᵖ C) {a b c : Bicategory.Adj B}
    (f : a ⟶ b) (g : b ⟶ c) :
    (F.mapAdj.mapComp f g).inv.τr =
      (F.mapComp g.r f.r).hom := sorry

/-- Forgetting to left adjoints after applying `mapAdj` agrees with first forgetting the
adjunctions and then applying the original pseudofunctor. -/
@[simp]
theorem mapAdj.comp_forget₁ (F : B ⥤ᵖ C) :
    F.mapAdj.comp (Bicategory.Adj.forget₁ (B := C)) =
      (Bicategory.Adj.forget₁ (B := B)).comp F := sorry

/-- Taking the left-adjoint isomorphism after mapping an isomorphism of adjunctions agrees
with mapping its original left-adjoint isomorphism. -/
@[simp]
theorem mapAdj.map₂Iso.lIso
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    {f g : a ⟶ b} (e : f ≅ g) :
    Bicategory.Adj.lIso (F.mapAdj.map₂Iso e) =
      F.map₂Iso (Bicategory.Adj.lIso e) := sorry

/-- Taking the right-adjoint isomorphism after mapping an isomorphism of adjunctions agrees
with mapping its original right-adjoint isomorphism. -/
@[simp]
theorem mapAdj.map₂Iso.rIso
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    {f g : a ⟶ b} (e : f ≅ g) :
    Bicategory.Adj.rIso (F.mapAdj.map₂Iso e) =
      F.map₂Iso (Bicategory.Adj.rIso e) := sorry

/-- The identity pseudofunctor induces the identity pseudofunctor on the bicategory of
adjunctions. -/
@[simp]
theorem mapAdj.id :
    (Pseudofunctor.id B).mapAdj =
      Pseudofunctor.id (Bicategory.Adj B) := sorry

section MapAdjComposition

variable {D : Type uD} [Bicategory.{wD, vD} D]

/-- The action on adjunctions induced by a composite pseudofunctor agrees with the composite
of the two induced actions. -/
@[simp]
theorem mapAdj.comp (F : B ⥤ᵖ C) (G : C ⥤ᵖ D) :
    (F.comp G).mapAdj =
      F.mapAdj.comp G.mapAdj := sorry

end MapAdjComposition

/- Data audit (mathlib 4.32): `mapAdj` stores mapped objects, both adjoint `1`-morphisms,
both mate components, and both directions of the identity and composition comparisons
explicitly. Its `sorryAx` is confined to Prop-valued mate and pseudofunctor coherence fields;
no adjunction, mate component, or comparison cell is selected from an existence witness. -/

end MapAdjunctionsImplementation

end Pseudofunctor

end CategoryTheory
