module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj

/-!
# Mapping bicategorical adjunctions

The explicit object, `1`-morphism, `2`-morphism, and comparison data induced
by a pseudofunctor on bicategories of adjunctions.
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

section MapAdjunctionsBasic

/-- The object of `Adj C` obtained by applying `F` to the object underlying an object of
`Adj B`. -/
@[stacks 0040 "object action on mapped bicategorical adjunctions"]
def mapAdj.object (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    Bicategory.Adj C :=
  ⟨F.obj a.obj⟩

/-- The object underlying the mapped object of the adjunction bicategory. -/
@[simp]
theorem mapAdj.object.obj (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    (mapAdj.object F a).obj = F.obj a.obj := sorry

/-- Map an adjunction through a pseudofunctor, regarded as a `1`-morphism between objects of
the adjunction bicategory. -/
@[stacks 0040 "morphism action on mapped bicategorical adjunctions"]
def mapAdj.hom (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    (f : a ⟶ b) : mapAdj.object F a ⟶ mapAdj.object F b :=
  ⟨F.mapAdjunction f.adj⟩

/-- The left adjoint underlying a mapped adjunction is the image of the original left
adjoint. -/
@[simp]
theorem mapAdj.hom.l (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (mapAdj.hom F f).l = F.map f.l := sorry

/-- The right adjoint underlying a mapped adjunction is the image of the original right
adjoint. -/
@[simp]
theorem mapAdj.hom.r (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (mapAdj.hom F f).r = F.map f.r := sorry

/-- The adjunction stored by a mapped `Adj`-morphism is the canonical mapped adjunction. -/
@[simp]
theorem mapAdj.hom.adj (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (mapAdj.hom F f).adj = F.mapAdjunction f.adj := sorry

/-- A pseudofunctor sends a mate pair to a mate pair between the mapped adjunctions. -/
theorem mapAdj.hom₂.conjugate
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    {f g : a ⟶ b} (η : f ⟶ g) :
    conjugateEquiv (mapAdj.hom F g).adj (mapAdj.hom F f).adj
        (F.map₂ η.τl) =
      F.map₂ η.τr := sorry

/-- Map a mate `2`-morphism through a pseudofunctor. Both mate components are mapped
explicitly; only their compatibility is proof-valued. -/
@[stacks 0040 "mate transformation action on mapped bicategorical adjunctions"]
def mapAdj.hom₂
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    {f g : a ⟶ b} (η : f ⟶ g) :
    mapAdj.hom F f ⟶ mapAdj.hom F g where
  τl := F.map₂ η.τl
  τr := F.map₂ η.τr
  conjugateEquiv_τl := mapAdj.hom₂.conjugate F η

/-- The left-adjoint component of a mapped mate transformation. -/
@[simp]
theorem mapAdj.hom₂.τl
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    {f g : a ⟶ b} (η : f ⟶ g) :
    (mapAdj.hom₂ F η).τl = F.map₂ η.τl := sorry

/-- The right-adjoint component of a mapped mate transformation. -/
@[simp]
theorem mapAdj.hom₂.τr
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    {f g : a ⟶ b} (η : f ⟶ g) :
    (mapAdj.hom₂ F η).τr = F.map₂ η.τr := sorry

/-- Mapping mate transformations preserves identity `2`-morphisms. -/
theorem mapAdj.hom₂.id
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    mapAdj.hom₂ F (𝟙 f) = 𝟙 (mapAdj.hom F f) := sorry

/-- Mapping mate transformations preserves vertical composition. -/
theorem mapAdj.hom₂.comp
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    mapAdj.hom₂ F (η ≫ θ) =
      mapAdj.hom₂ F η ≫ mapAdj.hom₂ F θ := sorry

/-- The functor on a hom-category of adjunctions induced by a pseudofunctor. -/
@[stacks 0040 "hom-category action on mapped bicategorical adjunctions"]
def mapAdj.hom.functor (F : B ⥤ᵖ C)
    (a b : Bicategory.Adj B) :
    (a ⟶ b) ⥤ (mapAdj.object F a ⟶ mapAdj.object F b) where
  obj := mapAdj.hom F
  map := mapAdj.hom₂ F
  map_id := mapAdj.hom₂.id F
  map_comp := mapAdj.hom₂.comp F

/-- The object action of the functor on a hom-category of adjunctions. -/
@[simp]
theorem mapAdj.hom.functor.obj
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (mapAdj.hom.functor F a b).obj f = mapAdj.hom F f := sorry

/-- The morphism action of the functor on a hom-category of adjunctions. -/
@[simp]
theorem mapAdj.hom.functor.map
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    {f g : a ⟶ b} (η : f ⟶ g) :
    (mapAdj.hom.functor F a b).map η = mapAdj.hom₂ F η := sorry

/-- The identity comparison of `F` and its inverse form a mate pair between the mapped
identity adjunction and the identity adjunction. -/
theorem mapAdj.mapIdIso.conjugate
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    conjugateEquiv
        (𝟙 (mapAdj.object F a) :
          mapAdj.object F a ⟶ mapAdj.object F a).adj
        (mapAdj.hom F (𝟙 a)).adj
        (F.mapId a.obj).hom =
      (F.mapId a.obj).inv := sorry

/-- The canonical identity comparison for the induced action on adjunctions. -/
@[stacks 0040 "identity comparison for mapped bicategorical adjunctions"]
def mapAdj.mapIdIso
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    mapAdj.hom F (𝟙 a) ≅ 𝟙 (mapAdj.object F a) :=
  Bicategory.Adj.iso₂Mk
    (F.mapId a.obj) (F.mapId a.obj).symm
    (mapAdj.mapIdIso.conjugate F a)

/-- The forward left-adjoint component of the identity comparison on adjunctions. -/
@[simp]
theorem mapAdj.mapIdIso.hom.τl
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    (mapAdj.mapIdIso F a).hom.τl =
      (F.mapId a.obj).hom := sorry

/-- The forward right-adjoint component of the identity comparison on adjunctions. -/
@[simp]
theorem mapAdj.mapIdIso.hom.τr
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    (mapAdj.mapIdIso F a).hom.τr =
      (F.mapId a.obj).inv := sorry

/-- The inverse left-adjoint component of the identity comparison on adjunctions. -/
@[simp]
theorem mapAdj.mapIdIso.inv.τl
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    (mapAdj.mapIdIso F a).inv.τl =
      (F.mapId a.obj).inv := sorry

/-- The inverse right-adjoint component of the identity comparison on adjunctions. -/
@[simp]
theorem mapAdj.mapIdIso.inv.τr
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    (mapAdj.mapIdIso F a).inv.τr =
      (F.mapId a.obj).hom := sorry

/-- The two composition comparisons of `F` form a mate pair between the mapped composite
adjunction and the composite of the mapped adjunctions. -/
theorem mapAdj.mapCompIso.conjugate
    (F : B ⥤ᵖ C) {a b c : Bicategory.Adj B}
    (f : a ⟶ b) (g : b ⟶ c) :
    conjugateEquiv
        (mapAdj.hom F f ≫ mapAdj.hom F g).adj
        (mapAdj.hom F (f ≫ g)).adj
        (F.mapComp f.l g.l).hom =
      (F.mapComp g.r f.r).inv := sorry

/-- The canonical composition comparison for the induced action on adjunctions. -/
@[stacks 0040 "composition comparison for mapped bicategorical adjunctions"]
def mapAdj.mapCompIso
    (F : B ⥤ᵖ C) {a b c : Bicategory.Adj B}
    (f : a ⟶ b) (g : b ⟶ c) :
    mapAdj.hom F (f ≫ g) ≅
      mapAdj.hom F f ≫ mapAdj.hom F g :=
  Bicategory.Adj.iso₂Mk
    (F.mapComp f.l g.l) (F.mapComp g.r f.r).symm
    (mapAdj.mapCompIso.conjugate F f g)

/-- The forward left-adjoint component of the composition comparison on adjunctions. -/
@[simp]
theorem mapAdj.mapCompIso.hom.τl
    (F : B ⥤ᵖ C) {a b c : Bicategory.Adj B}
    (f : a ⟶ b) (g : b ⟶ c) :
    (mapAdj.mapCompIso F f g).hom.τl =
      (F.mapComp f.l g.l).hom := sorry

/-- The forward right-adjoint component of the composition comparison on adjunctions. -/
@[simp]
theorem mapAdj.mapCompIso.hom.τr
    (F : B ⥤ᵖ C) {a b c : Bicategory.Adj B}
    (f : a ⟶ b) (g : b ⟶ c) :
    (mapAdj.mapCompIso F f g).hom.τr =
      (F.mapComp g.r f.r).inv := sorry

/-- The inverse left-adjoint component of the composition comparison on adjunctions. -/
@[simp]
theorem mapAdj.mapCompIso.inv.τl
    (F : B ⥤ᵖ C) {a b c : Bicategory.Adj B}
    (f : a ⟶ b) (g : b ⟶ c) :
    (mapAdj.mapCompIso F f g).inv.τl =
      (F.mapComp f.l g.l).inv := sorry

/-- The inverse right-adjoint component of the composition comparison on adjunctions. -/
@[simp]
theorem mapAdj.mapCompIso.inv.τr
    (F : B ⥤ᵖ C) {a b c : Bicategory.Adj B}
    (f : a ⟶ b) (g : b ⟶ c) :
    (mapAdj.mapCompIso F f g).inv.τr =
      (F.mapComp g.r f.r).hom := sorry

end MapAdjunctionsBasic

end Pseudofunctor

end CategoryTheory
