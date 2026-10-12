/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.MapAdjunctions.Mapping

/-!
# Pseudofunctorial action on mapped adjunctions

The pseudofunctor assembled from the pointwise hom-category action and its computation API.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

section MapAdjunctionsAction

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {D : Type uD} [Bicategory.{wD, vD} D]

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The implementation-level prelax action of adjunctions between pseudofunctors on
adjunction bicategories. -/
private def mapAdjunctions.prelax :
    PrelaxFunctor
      (Bicategory.Adj (Pseudofunctor B D))
      (Pseudofunctor (Bicategory.Adj B) (Bicategory.Adj D)) :=
  PrelaxFunctor.mkOfHomFunctors
    mapAdjunctions.object mapAdjunctions.hom.functor

/-- The canonical action on adjunctions between pseudofunctors preserves left
whiskering. -/
private theorem mapAdjunctions.map₂.whiskerLeft :
    ∀ {F G H : Bicategory.Adj (Pseudofunctor B D)}
      (f : F ⟶ G) {g h : G ⟶ H} (η : g ⟶ h),
      mapAdjunctions.prelax.map₂ (f ◁ η) =
        (mapAdjunctions.mapComp.iso f g).hom ≫
          mapAdjunctions.prelax.map f ◁
            mapAdjunctions.prelax.map₂ η ≫
          (mapAdjunctions.mapComp.iso f h).inv := sorry

/-- The canonical action on adjunctions between pseudofunctors preserves right
whiskering. -/
private theorem mapAdjunctions.map₂.whiskerRight :
    ∀ {F G H : Bicategory.Adj (Pseudofunctor B D)}
      {f g : F ⟶ G} (η : f ⟶ g) (h : G ⟶ H),
      mapAdjunctions.prelax.map₂ (η ▷ h) =
        (mapAdjunctions.mapComp.iso f h).hom ≫
          mapAdjunctions.prelax.map₂ η ▷
            mapAdjunctions.prelax.map h ≫
          (mapAdjunctions.mapComp.iso g h).inv := sorry

/-- The canonical action on adjunctions between pseudofunctors preserves the associator
modulo its composition comparisons. -/
private theorem mapAdjunctions.map₂.associator :
    ∀ {F G H I : Bicategory.Adj (Pseudofunctor B D)}
      (f : F ⟶ G) (g : G ⟶ H) (h : H ⟶ I),
      mapAdjunctions.prelax.map₂ (α_ f g h).hom =
        (mapAdjunctions.mapComp.iso (f ≫ g) h).hom ≫
          (mapAdjunctions.mapComp.iso f g).hom ▷
            mapAdjunctions.prelax.map h ≫
          (α_ (mapAdjunctions.prelax.map f)
            (mapAdjunctions.prelax.map g)
            (mapAdjunctions.prelax.map h)).hom ≫
          mapAdjunctions.prelax.map f ◁
            (mapAdjunctions.mapComp.iso g h).inv ≫
          (mapAdjunctions.mapComp.iso f (g ≫ h)).inv := sorry

/-- The canonical action on adjunctions between pseudofunctors preserves the left unitor
modulo its identity and composition comparisons. -/
private theorem mapAdjunctions.map₂.leftUnitor :
    ∀ {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G),
      mapAdjunctions.prelax.map₂ (λ_ f).hom =
        (mapAdjunctions.mapComp.iso (𝟙 F) f).hom ≫
          (mapAdjunctions.mapId.iso F).hom ▷
            mapAdjunctions.prelax.map f ≫
          (λ_ (mapAdjunctions.prelax.map f)).hom := sorry

/-- The canonical action on adjunctions between pseudofunctors preserves the right unitor
modulo its identity and composition comparisons. -/
private theorem mapAdjunctions.map₂.rightUnitor :
    ∀ {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G),
      mapAdjunctions.prelax.map₂ (ρ_ f).hom =
        (mapAdjunctions.mapComp.iso f (𝟙 G)).hom ≫
          mapAdjunctions.prelax.map f ◁
            (mapAdjunctions.mapId.iso G).hom ≫
          (ρ_ (mapAdjunctions.prelax.map f)).hom := sorry

end Implementation

variable (B D) in
/-- The canonical pseudofunctorial action of adjunctions between pseudofunctors on
adjunction bicategories.

An object is sent to its action on adjunctions. An adjunction between pseudofunctors is
sent to the strong transformation assembled from its pointwise adjunctions, and a mate
`2`-morphism is sent to the modification assembled from its pointwise mates. The source
and target bicategories are explicit because the resulting pseudofunctor has no other
data from which Lean can infer them. -/
@[stacks 0040 "action on adjunctions between pseudofunctors"]
def mapAdjunctions :
    Bicategory.Adj (Pseudofunctor B D) ⥤ᵖ
      Pseudofunctor (Bicategory.Adj B) (Bicategory.Adj D) where
  toPrelaxFunctor := Implementation.mapAdjunctions.prelax
  mapId := mapAdjunctions.mapId.iso
  mapComp := mapAdjunctions.mapComp.iso
  map₂_whisker_left := Implementation.mapAdjunctions.map₂.whiskerLeft
  map₂_whisker_right := Implementation.mapAdjunctions.map₂.whiskerRight
  map₂_associator := Implementation.mapAdjunctions.map₂.associator
  map₂_left_unitor := Implementation.mapAdjunctions.map₂.leftUnitor
  map₂_right_unitor := Implementation.mapAdjunctions.map₂.rightUnitor

/-- The object action of the canonical pseudofunctor on adjunctions between
pseudofunctors. -/
@[simp]
theorem mapAdjunctions.obj
    (F : Bicategory.Adj (Pseudofunctor B D)) :
    (mapAdjunctions B D).obj F = mapAdjunctions.object F := sorry

/-- Applying the object action again is the canonical image of an adjunction under the
underlying pseudofunctor. -/
@[simp]
theorem mapAdjunctions.object.obj
    (F : Bicategory.Adj (Pseudofunctor B D))
    (a : Bicategory.Adj B) :
    ((mapAdjunctions B D).obj F).obj a =
      mapAdj.object F.obj a := sorry

/-- The ambient object underlying the twice-evaluated object action. -/
@[simp]
theorem mapAdjunctions.object.carrier
    (F : Bicategory.Adj (Pseudofunctor B D))
    (a : Bicategory.Adj B) :
    (((mapAdjunctions B D).obj F).obj a).obj =
      F.obj.obj a.obj := sorry

/-- The `1`-morphism action of an object image is the canonical image of the source
adjunction. -/
@[simp]
theorem mapAdjunctions.object.map
    (F : Bicategory.Adj (Pseudofunctor B D))
    {a b : Bicategory.Adj B} (f : a ⟶ b) :
    ((mapAdjunctions B D).obj F).map f =
      mapAdj.hom F.obj f := sorry

/-- The left adjoint underlying the objectwise image of an adjunction. -/
@[simp]
theorem mapAdjunctions.object.map.l
    (F : Bicategory.Adj (Pseudofunctor B D))
    {a b : Bicategory.Adj B} (f : a ⟶ b) :
    (((mapAdjunctions B D).obj F).map f).l =
      F.obj.map f.l := sorry

/-- The right adjoint underlying the objectwise image of an adjunction. -/
@[simp]
theorem mapAdjunctions.object.map.r
    (F : Bicategory.Adj (Pseudofunctor B D))
    {a b : Bicategory.Adj B} (f : a ⟶ b) :
    (((mapAdjunctions B D).obj F).map f).r =
      F.obj.map f.r := sorry

/-- The adjunction underlying the objectwise image of an `Adj`-morphism. -/
@[simp]
theorem mapAdjunctions.object.map.adj
    (F : Bicategory.Adj (Pseudofunctor B D))
    {a b : Bicategory.Adj B} (f : a ⟶ b) :
    (((mapAdjunctions B D).obj F).map f).adj =
      F.obj.mapAdjunction f.adj := sorry

/-- The `2`-morphism action of an object image is the canonical image of a mate
transformation. -/
@[simp]
theorem mapAdjunctions.object.map₂
    (F : Bicategory.Adj (Pseudofunctor B D))
    {a b : Bicategory.Adj B} {f g : a ⟶ b} (γ : f ⟶ g) :
    ((mapAdjunctions B D).obj F).map₂ γ =
      mapAdj.hom₂ F.obj γ := sorry

/-- The left-adjoint component of the objectwise image of a mate transformation. -/
@[simp]
theorem mapAdjunctions.object.map₂.τl
    (F : Bicategory.Adj (Pseudofunctor B D))
    {a b : Bicategory.Adj B} {f g : a ⟶ b} (γ : f ⟶ g) :
    (((mapAdjunctions B D).obj F).map₂ γ).τl =
      F.obj.map₂ γ.τl := sorry

/-- The right-adjoint component of the objectwise image of a mate transformation. -/
@[simp]
theorem mapAdjunctions.object.map₂.τr
    (F : Bicategory.Adj (Pseudofunctor B D))
    {a b : Bicategory.Adj B} {f g : a ⟶ b} (γ : f ⟶ g) :
    (((mapAdjunctions B D).obj F).map₂ γ).τr =
      F.obj.map₂ γ.τr := sorry

/-- The hom-category action of an object image is the canonical mate-mapping functor. -/
@[simp]
theorem mapAdjunctions.object.mapFunctor
    (F : Bicategory.Adj (Pseudofunctor B D))
    (a b : Bicategory.Adj B) :
    ((mapAdjunctions B D).obj F).mapFunctor a b =
      mapAdj.hom.functor F.obj a b := sorry

/-- The identity comparison of an object image is the canonical mapped-adjunction
comparison. -/
@[simp]
theorem mapAdjunctions.object.mapId
    (F : Bicategory.Adj (Pseudofunctor B D))
    (a : Bicategory.Adj B) :
    ((mapAdjunctions B D).obj F).mapId a =
      mapAdj.mapIdIso F.obj a := sorry

/-- The composition comparison of an object image is the canonical mapped-adjunction
comparison. -/
@[simp]
theorem mapAdjunctions.object.mapComp
    (F : Bicategory.Adj (Pseudofunctor B D))
    {a b c : Bicategory.Adj B} (f : a ⟶ b) (g : b ⟶ c) :
    ((mapAdjunctions B D).obj F).mapComp f g =
      mapAdj.mapCompIso F.obj f g := sorry

/-- The `1`-morphism action of the canonical pseudofunctor on adjunctions between
pseudofunctors. -/
@[simp]
theorem mapAdjunctions.map
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G) :
    (mapAdjunctions B D).map f = mapAdjunctions.hom f := sorry

/-- The component of a mapped adjunction between pseudofunctors is its evaluated
pointwise adjunction. -/
@[simp]
theorem mapAdjunctions.map.app
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G)
    (a : Bicategory.Adj B) :
    ((mapAdjunctions B D).map f).app a =
      (mapAdjunctions.pointwiseAdjunction f).app a.obj := sorry

/-- The left adjoint underlying a component of a mapped adjunction is the corresponding
component of the original left adjoint strong transformation. -/
@[simp]
theorem mapAdjunctions.map.app.l
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G)
    (a : Bicategory.Adj B) :
    (((mapAdjunctions B D).map f).app a).l =
      f.l.app a.obj := sorry

/-- The right adjoint underlying a component of a mapped adjunction is the corresponding
component of the original right adjoint strong transformation. -/
@[simp]
theorem mapAdjunctions.map.app.r
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G)
    (a : Bicategory.Adj B) :
    (((mapAdjunctions B D).map f).app a).r =
      f.r.app a.obj := sorry

/-- The adjunction underlying a component of a mapped adjunction is its strict pointwise
evaluation. -/
@[simp]
theorem mapAdjunctions.map.app.adj
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G)
    (a : Bicategory.Adj B) :
    (((mapAdjunctions B D).map f).app a).adj =
      (evaluationAt D a.obj).mapAdjunction f.adj := sorry

/-- Naturality of a mapped adjunction is the pointwise mate-completed naturality
isomorphism. -/
@[simp]
theorem mapAdjunctions.map.naturality
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G)
    {a b : Bicategory.Adj B} (g : a ⟶ b) :
    ((mapAdjunctions B D).map f).naturality g =
      (mapAdjunctions.pointwiseAdjunction f).naturality g := sorry

/-- The forward left-adjoint naturality component of a mapped adjunction. -/
@[simp]
theorem mapAdjunctions.map.naturality.hom.τl
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G)
    {a b : Bicategory.Adj B} (g : a ⟶ b) :
    (((mapAdjunctions B D).map f).naturality g).hom.τl =
      (f.l.naturality g.l).hom := sorry

/-- The inverse left-adjoint naturality component of a mapped adjunction. -/
@[simp]
theorem mapAdjunctions.map.naturality.inv.τl
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G)
    {a b : Bicategory.Adj B} (g : a ⟶ b) :
    (((mapAdjunctions B D).map f).naturality g).inv.τl =
      (f.l.naturality g.l).inv := sorry

/-- The forward right-adjoint naturality component of a mapped adjunction. -/
@[simp]
theorem mapAdjunctions.map.naturality.hom.τr
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G)
    {a b : Bicategory.Adj B} (g : a ⟶ b) :
    (((mapAdjunctions B D).map f).naturality g).hom.τr =
      (f.r.naturality g.r).hom := sorry

/-- The inverse right-adjoint naturality component of a mapped adjunction. -/
@[simp]
theorem mapAdjunctions.map.naturality.inv.τr
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G)
    {a b : Bicategory.Adj B} (g : a ⟶ b) :
    (((mapAdjunctions B D).map f).naturality g).inv.τr =
      (f.r.naturality g.r).inv := sorry

/-- The `2`-morphism action of the canonical pseudofunctor on mate transformations. -/
@[simp]
theorem mapAdjunctions.map₂
    {F G : Bicategory.Adj (Pseudofunctor B D)}
    {f g : F ⟶ G} (γ : f ⟶ g) :
    (mapAdjunctions B D).map₂ γ = mapAdjunctions.hom₂ γ := sorry

/-- The left-adjoint component of a mapped mate transformation is evaluated
pointwise. -/
@[simp]
theorem mapAdjunctions.map₂.app.τl
    {F G : Bicategory.Adj (Pseudofunctor B D)}
    {f g : F ⟶ G} (γ : f ⟶ g) (a : Bicategory.Adj B) :
    (((mapAdjunctions B D).map₂ γ).as.app a).τl =
      γ.τl.as.app a.obj := sorry

/-- The right-adjoint component of a mapped mate transformation is evaluated
pointwise. -/
@[simp]
theorem mapAdjunctions.map₂.app.τr
    {F G : Bicategory.Adj (Pseudofunctor B D)}
    {f g : F ⟶ G} (γ : f ⟶ g) (a : Bicategory.Adj B) :
    (((mapAdjunctions B D).map₂ γ).as.app a).τr =
      γ.τr.as.app a.obj := sorry

/-- The hom-category action of the canonical pseudofunctor is the pointwise mate-mapping
functor. -/
@[simp]
theorem mapAdjunctions.mapFunctor
    (F G : Bicategory.Adj (Pseudofunctor B D)) :
    (mapAdjunctions B D).mapFunctor F G =
      mapAdjunctions.hom.functor F G := sorry

/-- The identity comparison of the canonical pseudofunctor. -/
@[simp]
theorem mapAdjunctions.mapId
    (F : Bicategory.Adj (Pseudofunctor B D)) :
    (mapAdjunctions B D).mapId F =
      mapAdjunctions.mapId.iso F := sorry

/-- The forward component of the canonical identity comparison at a source
adjunction. -/
@[simp]
theorem mapAdjunctions.mapId.hom.app
    (F : Bicategory.Adj (Pseudofunctor B D))
    (a : Bicategory.Adj B) :
    ((mapAdjunctions B D).mapId F).hom.as.app a =
      (mapAdjunctions.mapId.iso F).hom.as.app a := sorry

/-- The inverse component of the canonical identity comparison at a source
adjunction. -/
@[simp]
theorem mapAdjunctions.mapId.inv.app
    (F : Bicategory.Adj (Pseudofunctor B D))
    (a : Bicategory.Adj B) :
    ((mapAdjunctions B D).mapId F).inv.as.app a =
      (mapAdjunctions.mapId.iso F).inv.as.app a := sorry

/-- The forward left-adjoint component of the canonical identity comparison. -/
@[simp]
theorem mapAdjunctions.mapId.hom.app.τl
    (F : Bicategory.Adj (Pseudofunctor B D))
    (a : Bicategory.Adj B) :
    (((mapAdjunctions B D).mapId F).hom.as.app a).τl =
      𝟙 _ := sorry

/-- The forward right-adjoint component of the canonical identity comparison. -/
@[simp]
theorem mapAdjunctions.mapId.hom.app.τr
    (F : Bicategory.Adj (Pseudofunctor B D))
    (a : Bicategory.Adj B) :
    (((mapAdjunctions B D).mapId F).hom.as.app a).τr =
      𝟙 _ := sorry

/-- The inverse left-adjoint component of the canonical identity comparison. -/
@[simp]
theorem mapAdjunctions.mapId.inv.app.τl
    (F : Bicategory.Adj (Pseudofunctor B D))
    (a : Bicategory.Adj B) :
    (((mapAdjunctions B D).mapId F).inv.as.app a).τl =
      𝟙 _ := sorry

/-- The inverse right-adjoint component of the canonical identity comparison. -/
@[simp]
theorem mapAdjunctions.mapId.inv.app.τr
    (F : Bicategory.Adj (Pseudofunctor B D))
    (a : Bicategory.Adj B) :
    (((mapAdjunctions B D).mapId F).inv.as.app a).τr =
      𝟙 _ := sorry

/-- The composition comparison of the canonical pseudofunctor. -/
@[simp]
theorem mapAdjunctions.mapComp
    {F G H : Bicategory.Adj (Pseudofunctor B D)}
    (f : F ⟶ G) (g : G ⟶ H) :
    (mapAdjunctions B D).mapComp f g =
      mapAdjunctions.mapComp.iso f g := sorry

/-- The forward component of the canonical composition comparison at a source
adjunction. -/
@[simp]
theorem mapAdjunctions.mapComp.hom.app
    {F G H : Bicategory.Adj (Pseudofunctor B D)}
    (f : F ⟶ G) (g : G ⟶ H) (a : Bicategory.Adj B) :
    ((mapAdjunctions B D).mapComp f g).hom.as.app a =
      (mapAdjunctions.mapComp.iso f g).hom.as.app a := sorry

/-- The inverse component of the canonical composition comparison at a source
adjunction. -/
@[simp]
theorem mapAdjunctions.mapComp.inv.app
    {F G H : Bicategory.Adj (Pseudofunctor B D)}
    (f : F ⟶ G) (g : G ⟶ H) (a : Bicategory.Adj B) :
    ((mapAdjunctions B D).mapComp f g).inv.as.app a =
      (mapAdjunctions.mapComp.iso f g).inv.as.app a := sorry

/-- The forward left-adjoint component of the canonical composition comparison. -/
@[simp]
theorem mapAdjunctions.mapComp.hom.app.τl
    {F G H : Bicategory.Adj (Pseudofunctor B D)}
    (f : F ⟶ G) (g : G ⟶ H) (a : Bicategory.Adj B) :
    (((mapAdjunctions B D).mapComp f g).hom.as.app a).τl =
      𝟙 _ := sorry

/-- The forward right-adjoint component of the canonical composition comparison. -/
@[simp]
theorem mapAdjunctions.mapComp.hom.app.τr
    {F G H : Bicategory.Adj (Pseudofunctor B D)}
    (f : F ⟶ G) (g : G ⟶ H) (a : Bicategory.Adj B) :
    (((mapAdjunctions B D).mapComp f g).hom.as.app a).τr =
      𝟙 _ := sorry

/-- The inverse left-adjoint component of the canonical composition comparison. -/
@[simp]
theorem mapAdjunctions.mapComp.inv.app.τl
    {F G H : Bicategory.Adj (Pseudofunctor B D)}
    (f : F ⟶ G) (g : G ⟶ H) (a : Bicategory.Adj B) :
    (((mapAdjunctions B D).mapComp f g).inv.as.app a).τl =
      𝟙 _ := sorry

/-- The inverse right-adjoint component of the canonical composition comparison. -/
@[simp]
theorem mapAdjunctions.mapComp.inv.app.τr
    {F G H : Bicategory.Adj (Pseudofunctor B D)}
    (f : F ⟶ G) (g : G ⟶ H) (a : Bicategory.Adj B) :
    (((mapAdjunctions B D).mapComp f g).inv.as.app a).τr =
      𝟙 _ := sorry

/- Data audit (mathlib 4.32): `mapAdjunctions` has explicit object, `1`-morphism, and
`2`-morphism actions. Its identity and composition comparisons specialize
`PointwiseAdjunction.mapAdj.idIso` and `.compIso`; every component therefore has explicit
identity mate data. No comparison morphism is selected through an existential witness.
The `sorryAx` in these owners comes from mate/modification coherence and the five
pseudofunctor coherence proof fields, as well as proof fields
inherited from the existing `Pseudofunctor.mapAdj` owner. -/

end MapAdjunctionsAction

end Pseudofunctor

end CategoryTheory
