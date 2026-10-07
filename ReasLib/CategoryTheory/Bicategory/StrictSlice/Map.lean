module

public import ReasLib.CategoryTheory.Bicategory.StrictSlice
import Mathlib.Tactic.CrossRefAttribute

/-!
# Mapping strict slices

A strict pseudofunctor `F : C ⟶ D` sends an object over `X` to an object over
`F.obj X`.  This file makes that construction functorial on strict slices.

The namespace `StrictSlice.Map` owns the explicit object, `1`-morphism, and
`2`-morphism data.  The declaration `StrictSlice.map` packages these data as a
strict pseudofunctor.  This separation lets downstream constructions reuse the
individual layers without unpacking the bundled pseudofunctor.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe wC vC uC wD vD uD

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace Bicategory.StrictSlice

variable {C : Type uC} [Bicategory.{wC, vC} C] [Bicategory.Strict C]
variable {D : Type uD} [Bicategory.{wD, vD} D] [Bicategory.Strict D]

namespace Map

variable (F : StrictPseudofunctor C D) {X : C}

/-- Apply `F` to the domain and structural arrow of a strict-slice object. -/
def obj (S : StrictSlice X) : StrictSlice (F.obj X) :=
  StrictSlice.mk (F.obj S.obj) (F.map S.hom)

/-- The domain of a mapped strict-slice object is the image of the original domain. -/
@[simp]
theorem obj_obj (S : StrictSlice X) :
    (obj F S).obj = F.obj S.obj := sorry

/-- The structural arrow of a mapped strict-slice object is the image of the original
structural arrow. -/
@[simp]
theorem obj_hom (S : StrictSlice X) :
    (obj F S).hom = F.map S.hom := sorry

/-- Applying `F` to the ambient map of a strict-slice morphism gives a commuting triangle
between the mapped objects. -/
theorem hom_comm {S T : StrictSlice X} (f : S ⟶ T) :
    F.map (StrictSlice.Hom.hom f) ≫ (obj F T).hom = (obj F S).hom := sorry

/-- Apply `F` to the ambient map of a strict-slice morphism. -/
def hom {S T : StrictSlice X} (f : S ⟶ T) : obj F S ⟶ obj F T :=
  StrictSlice.Hom.mk (F.map (StrictSlice.Hom.hom f)) (hom_comm F f)

/-- The ambient map of a mapped strict-slice morphism is the image of its original ambient
map. -/
@[simp]
theorem hom_hom {S T : StrictSlice X} (f : S ⟶ T) :
    StrictSlice.Hom.hom (hom F f) = F.map (StrictSlice.Hom.hom f) := sorry

/-- Applying `F.map₂` to the ambient cell of a strict-slice `2`-morphism is compatible with
the mapped commuting triangles. -/
theorem hom₂_comm {S T : StrictSlice X} {f g : S ⟶ T} (eta : f ⟶ g) :
    F.map₂ (StrictSlice.Hom₂.hom eta) ▷ (obj F T).hom ≫
        eqToHom (StrictSlice.Hom.comm (hom F g)) =
      eqToHom (StrictSlice.Hom.comm (hom F f)) := sorry

/-- Apply `F.map₂` to the ambient cell of a strict-slice `2`-morphism. -/
def hom₂ {S T : StrictSlice X} {f g : S ⟶ T} (eta : f ⟶ g) :
    hom F f ⟶ hom F g :=
  StrictSlice.Hom₂.mk (F.map₂ (StrictSlice.Hom₂.hom eta)) (hom₂_comm F eta)

/-- The ambient cell of a mapped strict-slice `2`-morphism is the image of its original
ambient cell. -/
@[simp]
theorem hom₂_hom {S T : StrictSlice X} {f g : S ⟶ T} (eta : f ⟶ g) :
    StrictSlice.Hom₂.hom (hom₂ F eta) =
      F.map₂ (StrictSlice.Hom₂.hom eta) := sorry

/-- Mapping strict-slice morphisms preserves identities strictly. -/
private theorem hom_id (S : StrictSlice X) :
    hom F (𝟙 S) = 𝟙 (obj F S) := sorry

/-- Mapping strict-slice morphisms preserves composition strictly. -/
private theorem hom_comp {R S T : StrictSlice X} (f : R ⟶ S) (g : S ⟶ T) :
    hom F (f ≫ g) = hom F f ≫ hom F g := sorry

/-- Mapping strict-slice `2`-morphisms preserves identity cells. -/
private theorem hom₂_id {S T : StrictSlice X} (f : S ⟶ T) :
    hom₂ F (𝟙 f) = 𝟙 (hom F f) := sorry

/-- Mapping strict-slice `2`-morphisms preserves vertical composition. -/
private theorem hom₂_comp {S T : StrictSlice X} {f g h : S ⟶ T}
    (eta : f ⟶ g) (theta : g ⟶ h) :
    hom₂ F (eta ≫ theta) = hom₂ F eta ≫ hom₂ F theta := sorry

/-- Mapping strict-slice `2`-morphisms is compatible with left whiskering. -/
private theorem hom₂_whisker_left {R S T : StrictSlice X} (f : R ⟶ S)
    {g h : S ⟶ T} (eta : g ⟶ h) :
    hom₂ F (f ◁ eta) =
      eqToHom (hom_comp F f g) ≫
        hom F f ◁ hom₂ F eta ≫
          eqToHom (hom_comp F f h).symm := sorry

/-- Mapping strict-slice `2`-morphisms is compatible with right whiskering. -/
private theorem hom₂_whisker_right {R S T : StrictSlice X} {f g : R ⟶ S}
    (eta : f ⟶ g) (h : S ⟶ T) :
    hom₂ F (eta ▷ h) =
      eqToHom (hom_comp F f h) ≫
        hom₂ F eta ▷ hom F h ≫
          eqToHom (hom_comp F g h).symm := sorry

/-- The strict-pseudofunctor pre-core induced by applying `F` to every layer of a strict
slice.  All non-Prop fields are the explicit owners `obj`, `hom`, and `hom₂`. -/
private def preCore (X : C) :
    StrictPseudofunctorPreCore (StrictSlice X) (StrictSlice (F.obj X)) where
  obj := obj F
  map := hom F
  map₂ := hom₂ F
  map_id := hom_id F
  map_comp := hom_comp F
  map₂_id := hom₂_id F
  map₂_comp := hom₂_comp F
  map₂_whisker_left := hom₂_whisker_left F
  map₂_whisker_right := hom₂_whisker_right F

end Map

/-- A strict pseudofunctor induces a strict pseudofunctor between strict slices by applying it
to every domain, structural arrow, ambient map, and ambient cell. -/
def map (F : StrictPseudofunctor C D) (X : C) :
    StrictPseudofunctor (StrictSlice X) (StrictSlice (F.obj X)) :=
  StrictPseudofunctor.mk'' (Map.preCore F X)

namespace map

/-- The object action of strict-slice mapping is `Map.obj`. -/
@[simp]
theorem obj (F : StrictPseudofunctor C D) (X : C) (S : StrictSlice X) :
    (StrictSlice.map F X).obj S = Map.obj F S := sorry

/-- Strict-slice mapping applies `F.obj` to the domain of an object. -/
@[simp]
theorem obj_obj (F : StrictPseudofunctor C D) (X : C) (S : StrictSlice X) :
    ((StrictSlice.map F X).obj S).obj = F.obj S.obj := sorry

/-- Strict-slice mapping applies `F.map` to the structural arrow of an object. -/
@[simp]
theorem obj_hom (F : StrictPseudofunctor C D) (X : C) (S : StrictSlice X) :
    ((StrictSlice.map F X).obj S).hom = F.map S.hom := sorry

/-- The `1`-morphism action of strict-slice mapping is `Map.hom`. -/
@[simp]
theorem hom (F : StrictPseudofunctor C D) (X : C)
    {S T : StrictSlice X} (f : S ⟶ T) :
    (StrictSlice.map F X).map f = Map.hom F f := sorry

/-- The ambient map of the image of a strict-slice morphism is the image under `F.map` of its
ambient map. -/
@[simp]
theorem hom_hom (F : StrictPseudofunctor C D) (X : C)
    {S T : StrictSlice X} (f : S ⟶ T) :
    StrictSlice.Hom.hom ((StrictSlice.map F X).map f) =
      F.map (StrictSlice.Hom.hom f) := sorry

/-- The `2`-morphism action of strict-slice mapping is `Map.hom₂`. -/
@[simp]
theorem hom₂ (F : StrictPseudofunctor C D) (X : C)
    {S T : StrictSlice X} {f g : S ⟶ T} (eta : f ⟶ g) :
    (StrictSlice.map F X).map₂ eta = Map.hom₂ F eta := sorry

/-- The ambient cell of the image of a strict-slice `2`-morphism is the image under `F.map₂`
of its ambient cell. -/
@[simp]
theorem hom₂_hom (F : StrictPseudofunctor C D) (X : C)
    {S T : StrictSlice X} {f g : S ⟶ T} (eta : f ⟶ g) :
    StrictSlice.Hom₂.hom ((StrictSlice.map F X).map₂ eta) =
      F.map₂ (StrictSlice.Hom₂.hom eta) := sorry

end map

end Bicategory.StrictSlice

end CategoryTheory
