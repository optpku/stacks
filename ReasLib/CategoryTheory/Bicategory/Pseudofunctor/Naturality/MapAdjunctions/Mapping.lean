/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseAdjunction.Action.Coherence
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseAdjunction.Action.Modification
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseAdjunction.Constructors

/-!
# Pointwise comparison data for mapped adjunctions

The hom-category action and comparison isomorphisms underlying the canonical action on
adjunctions between pseudofunctors.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

section MapAdjunctionsNaturality

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {D : Type uD} [Bicategory.{wD, vD} D]

/-- The image of a pseudofunctor, regarded as an object of the adjunction bicategory, under
the canonical action on adjunctions. -/
@[stacks 0040 "object action on adjunctions between pseudofunctors"]
def mapAdjunctions.object
    (F : Bicategory.Adj (Pseudofunctor B D)) :
    Pseudofunctor (Bicategory.Adj B) (Bicategory.Adj D) :=
  F.obj.mapAdj

/-- The pointwise adjunction obtained from an adjunction between strong transformations. -/
@[stacks 0040 "pointwise adjunction between mapped pseudofunctors"]
def mapAdjunctions.pointwiseAdjunction
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G) :
    StrongTrans.PointwiseAdjunction f.l :=
  StrongTrans.PointwiseAdjunction.ofAdjunction f.adj

/-- The chosen pointwise right adjoint is the corresponding component of the right adjoint
strong transformation. -/
@[simp]
theorem mapAdjunctions.pointwiseAdjunction.rightApp
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G)
    (a : B) :
    (mapAdjunctions.pointwiseAdjunction f).rightApp a =
      f.r.app a := sorry

/-- The chosen pointwise adjunction is obtained by strict evaluation of the original
adjunction. -/
@[simp]
theorem mapAdjunctions.pointwiseAdjunction.adj
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G)
    (a : B) :
    (mapAdjunctions.pointwiseAdjunction f).adj a =
      (evaluationAt D a).mapAdjunction f.adj := sorry

/-- An adjunction between strong transformations induces a strong transformation between
their canonical actions on adjunctions. -/
@[stacks 0040 "morphism action on adjunctions between pseudofunctors"]
def mapAdjunctions.hom
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G) :
    mapAdjunctions.object F ⟶ mapAdjunctions.object G :=
  (mapAdjunctions.pointwiseAdjunction f).mapAdj

/-- The component of the induced strong transformation is the evaluated component
adjunction. -/
@[simp]
theorem mapAdjunctions.hom.app
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G)
    (a : Bicategory.Adj B) :
    (mapAdjunctions.hom f).app a =
      (mapAdjunctions.pointwiseAdjunction f).app a.obj := sorry

/-- The left adjoint of an induced component is the corresponding component of the original
left adjoint strong transformation. -/
@[simp]
theorem mapAdjunctions.hom.app.l
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G)
    (a : Bicategory.Adj B) :
    ((mapAdjunctions.hom f).app a).l =
      f.l.app a.obj := sorry

/-- The right adjoint of an induced component is the corresponding component of the original
right adjoint strong transformation. -/
@[simp]
theorem mapAdjunctions.hom.app.r
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G)
    (a : Bicategory.Adj B) :
    ((mapAdjunctions.hom f).app a).r =
      f.r.app a.obj := sorry

/-- The left-adjoint naturality cell of an induced strong transformation is the evaluated
naturality cell of the original left adjoint transformation. -/
@[simp]
theorem mapAdjunctions.hom.naturality.τl.forward
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G)
    {a b : Bicategory.Adj B} (g : a ⟶ b) :
    ((mapAdjunctions.hom f).naturality g).hom.τl =
      (f.l.naturality g.l).hom := sorry

/-- The inverse left-adjoint naturality cell of an induced strong transformation. -/
@[simp]
theorem mapAdjunctions.hom.naturality.τl.backward
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G)
    {a b : Bicategory.Adj B} (g : a ⟶ b) :
    ((mapAdjunctions.hom f).naturality g).inv.τl =
      (f.l.naturality g.l).inv := sorry

/-- The right-adjoint naturality cell is the corresponding naturality cell of the right
adjoint strong transformation. -/
@[simp]
theorem mapAdjunctions.hom.naturality.τr.forward
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G)
    {a b : Bicategory.Adj B} (g : a ⟶ b) :
    ((mapAdjunctions.hom f).naturality g).hom.τr =
      (f.r.naturality g.r).hom := sorry

/-- The inverse right-adjoint naturality cell is the inverse naturality cell of the right
adjoint strong transformation. -/
@[simp]
theorem mapAdjunctions.hom.naturality.τr.backward
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G)
    {a b : Bicategory.Adj B} (g : a ⟶ b) :
    ((mapAdjunctions.hom f).naturality g).inv.τr =
      (f.r.naturality g.r).inv := sorry

/-- A mate `2`-morphism between adjunctions of strong transformations induces a modification
between their actions on adjunctions. -/
@[stacks 0040 "2-morphism action on adjunctions between pseudofunctors"]
def mapAdjunctions.hom₂
    {F G : Bicategory.Adj (Pseudofunctor B D)}
    {f g : F ⟶ G} (γ : f ⟶ g) :
    mapAdjunctions.hom f ⟶ mapAdjunctions.hom g :=
  StrongTrans.PointwiseAdjunction.mapAdj.map₂
    (mapAdjunctions.pointwiseAdjunction f)
    (mapAdjunctions.pointwiseAdjunction g) γ.τl

/-- The left-adjoint component of an induced modification is the evaluated original mate
component. -/
@[simp]
theorem mapAdjunctions.hom₂.app.τl
    {F G : Bicategory.Adj (Pseudofunctor B D)}
    {f g : F ⟶ G} (γ : f ⟶ g)
    (a : Bicategory.Adj B) :
    ((mapAdjunctions.hom₂ γ).as.app a).τl =
      γ.τl.as.app a.obj := sorry

/-- The right-adjoint component of an induced modification is the evaluated original right
mate component. -/
@[simp]
theorem mapAdjunctions.hom₂.app.τr
    {F G : Bicategory.Adj (Pseudofunctor B D)}
    {f g : F ⟶ G} (γ : f ⟶ g)
    (a : Bicategory.Adj B) :
    ((mapAdjunctions.hom₂ γ).as.app a).τr =
      γ.τr.as.app a.obj := sorry

/-- Mapping mate `2`-morphisms between adjunctions of strong transformations preserves
identities. -/
theorem mapAdjunctions.hom₂.id
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G) :
    mapAdjunctions.hom₂ (𝟙 f) =
      𝟙 (mapAdjunctions.hom f) := sorry

/-- Mapping mate `2`-morphisms between adjunctions of strong transformations preserves
vertical composition. -/
theorem mapAdjunctions.hom₂.comp
    {F G : Bicategory.Adj (Pseudofunctor B D)}
    {f g h : F ⟶ G} (γ : f ⟶ g) (δ : g ⟶ h) :
    mapAdjunctions.hom₂ (γ ≫ δ) =
      mapAdjunctions.hom₂ γ ≫ mapAdjunctions.hom₂ δ := sorry

/-- The functor on hom-categories induced by the canonical action on adjunctions. -/
@[stacks 0040 "hom-category action on adjunctions between pseudofunctors"]
def mapAdjunctions.hom.functor
    (F G : Bicategory.Adj (Pseudofunctor B D)) :
    (F ⟶ G) ⥤
      (mapAdjunctions.object F ⟶ mapAdjunctions.object G) where
  obj := mapAdjunctions.hom
  map := mapAdjunctions.hom₂
  map_id := mapAdjunctions.hom₂.id
  map_comp := mapAdjunctions.hom₂.comp

/-- The object action of the induced hom-category functor. -/
@[simp]
theorem mapAdjunctions.hom.functor.obj
    {F G : Bicategory.Adj (Pseudofunctor B D)} (f : F ⟶ G) :
    (mapAdjunctions.hom.functor F G).obj f =
      mapAdjunctions.hom f := sorry

/-- The morphism action of the induced hom-category functor. -/
@[simp]
theorem mapAdjunctions.hom.functor.map
    {F G : Bicategory.Adj (Pseudofunctor B D)}
    {f g : F ⟶ G} (γ : f ⟶ g) :
    (mapAdjunctions.hom.functor F G).map γ =
      mapAdjunctions.hom₂ γ := sorry

/-- The identity comparison for the canonical action of adjunctions between
pseudofunctors, obtained by comparing the two chosen pointwise identity
adjunctions and then applying the general action coherence. -/
@[stacks 0040 "identity comparison for the action on adjunctions between pseudofunctors"]
def mapAdjunctions.mapId.iso
    (F : Bicategory.Adj (Pseudofunctor B D)) :
    mapAdjunctions.hom (𝟙 F) ≅
      𝟙 (mapAdjunctions.object F) :=
  StrongTrans.PointwiseAdjunction.mapAdj.mapIso
      (mapAdjunctions.pointwiseAdjunction (𝟙 F))
      (StrongTrans.PointwiseAdjunction.id F.obj) (Iso.refl _) ≪≫
    StrongTrans.PointwiseAdjunction.mapAdj.idIso F.obj

/-- The composition comparison for the canonical action of adjunctions between
pseudofunctors, obtained by comparing the two chosen pointwise composite
adjunctions and then applying the general action coherence. -/
@[stacks 0040 "composition comparison for the action on adjunctions between pseudofunctors"]
def mapAdjunctions.mapComp.iso
    {F G H : Bicategory.Adj (Pseudofunctor B D)}
    (f : F ⟶ G) (g : G ⟶ H) :
    mapAdjunctions.hom (f ≫ g) ≅
      mapAdjunctions.hom f ≫ mapAdjunctions.hom g :=
  StrongTrans.PointwiseAdjunction.mapAdj.mapIso
      (mapAdjunctions.pointwiseAdjunction (f ≫ g))
      (StrongTrans.PointwiseAdjunction.comp
        (mapAdjunctions.pointwiseAdjunction f)
        (mapAdjunctions.pointwiseAdjunction g)) (Iso.refl _) ≪≫
    StrongTrans.PointwiseAdjunction.mapAdj.compIso
      (mapAdjunctions.pointwiseAdjunction f)
      (mapAdjunctions.pointwiseAdjunction g)

end MapAdjunctionsNaturality

end Pseudofunctor

end CategoryTheory
