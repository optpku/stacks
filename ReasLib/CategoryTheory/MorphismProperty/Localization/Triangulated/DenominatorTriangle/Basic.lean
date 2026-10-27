/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.MorphismProperty.Localization.Triangulated

/-!
# Denominators under a triangle

For a morphism property `W` and a triangle `T`, this file defines the full subcategory of
`Under T` consisting of morphisms to distinguished triangles whose three components belong to
`W`.  It also provides the three canonical projections to the denominator categories under the
vertices of `T`.
-/

@[expose] public section

open CategoryTheory.ObjectProperty CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] [Limits.HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

namespace TriangleDenominator

/-- The property of a morphism of triangles `U : Under T` having distinguished target and all
three components in `W`. -/
@[stacks 05R9 "denominators under a distinguished triangle"]
def objectProperty (W : MorphismProperty C) (T : Triangle C) :
    ObjectProperty (CategoryTheory.Under T) :=
  fun U ↦ U.right ∈ distTriang C ∧ W U.hom.hom₁ ∧ W U.hom.hom₂ ∧ W U.hom.hom₃

/-- Membership in `objectProperty W T` is the conjunction of distinguishedness of the target
and membership of the three structural components in `W`. -/
theorem objectProperty_iff (W : MorphismProperty C) (T : Triangle C)
    (U : CategoryTheory.Under T) :
    objectProperty W T U ↔
      U.right ∈ distTriang C ∧ W U.hom.hom₁ ∧ W U.hom.hom₂ ∧ W U.hom.hom₃ := Iff.rfl

/-- The target distinguishedness condition extracted from the unbundled object property. -/
theorem target_distinguished_of_property (W : MorphismProperty C) (T : Triangle C)
    {U : CategoryTheory.Under T} (hU : objectProperty W T U) :
    U.right ∈ distTriang C := hU.1

/-- The first-component condition extracted from the unbundled object property. -/
theorem hom₁_mem_of_property (W : MorphismProperty C) (T : Triangle C)
    {U : CategoryTheory.Under T} (hU : objectProperty W T U) : W U.hom.hom₁ := hU.2.1

/-- The second-component condition extracted from the unbundled object property. -/
theorem hom₂_mem_of_property (W : MorphismProperty C) (T : Triangle C)
    {U : CategoryTheory.Under T} (hU : objectProperty W T U) : W U.hom.hom₂ := hU.2.2.1

/-- The third-component condition extracted from the unbundled object property. -/
theorem hom₃_mem_of_property (W : MorphismProperty C) (T : Triangle C)
    {U : CategoryTheory.Under T} (hU : objectProperty W T U) : W U.hom.hom₃ := hU.2.2.2

end TriangleDenominator

/-- The category of morphisms from `T` to distinguished triangles whose three components belong
to `W`. -/
@[stacks 05R9 "denominators under a distinguished triangle"]
abbrev TriangleDenominator (W : MorphismProperty C) (T : Triangle C) :=
  (TriangleDenominator.objectProperty W T).FullSubcategory

namespace TriangleDenominator

/-- Construct a triangle denominator from an underlying arrow of triangles and its four defining
properties. -/
def mk (W : MorphismProperty C) (T : Triangle C) (U : CategoryTheory.Under T)
    (hU : U.right ∈ distTriang C) (h₁ : W U.hom.hom₁) (h₂ : W U.hom.hom₂)
    (h₃ : W U.hom.hom₃) : TriangleDenominator W T :=
  ⟨U, hU, h₁, h₂, h₃⟩

/-- The underlying object of a triangle denominator built by `mk` is the supplied under-object. -/
@[simp]
theorem mk_obj (W : MorphismProperty C) (T : Triangle C)
    (U : CategoryTheory.Under T)
    (hU : U.right ∈ distTriang C) (h₁ : W U.hom.hom₁) (h₂ : W U.hom.hom₂)
    (h₃ : W U.hom.hom₃) :
    (mk W T U hU h₁ h₂ h₃).obj = U := rfl

/-- The target triangle of a triangle denominator is distinguished. -/
theorem target_distinguished (W : MorphismProperty C) (T : Triangle C)
    (U : TriangleDenominator W T) : U.obj.right ∈ distTriang C := U.property.1

/-- The first component of a triangle denominator belongs to `W`. -/
theorem hom₁_mem (W : MorphismProperty C) (T : Triangle C)
    (U : TriangleDenominator W T) : W U.obj.hom.hom₁ := U.property.2.1

/-- The second component of a triangle denominator belongs to `W`. -/
theorem hom₂_mem (W : MorphismProperty C) (T : Triangle C)
    (U : TriangleDenominator W T) : W U.obj.hom.hom₂ := U.property.2.2.1

/-- The third component of a triangle denominator belongs to `W`. -/
theorem hom₃_mem (W : MorphismProperty C) (T : Triangle C)
    (U : TriangleDenominator W T) : W U.obj.hom.hom₃ := U.property.2.2.2

/-- Naturality of the structural arrows obtained by applying a functor to an under-object. -/
theorem projectionToUnder_naturality (T : Triangle C) (F : Triangle C ⥤ C)
    {U V : CategoryTheory.Under T} (f : U ⟶ V) :
    F.map U.hom ≫ F.map f.right = F.map V.hom := by
  rw [← F.map_comp, CategoryTheory.Under.w f]

/-- Applying `F : Triangle C ⥤ C` to structural arrows gives a functor from `Under T` to the
under-category of `F.obj T`. -/
def projectionToUnder (T : Triangle C) (F : Triangle C ⥤ C) :
    CategoryTheory.Under T ⥤ CategoryTheory.Under (F.obj T) :=
  Functor.toUnder (CategoryTheory.Under.forget T ⋙ F) (F.obj T) (fun U ↦ F.map U.hom)
    (fun {_ _} f ↦ projectionToUnder_naturality T F f)

/-- The target of `projectionToUnder` is obtained by applying the projection functor. -/
@[simp]
theorem projectionToUnder_obj_right (T : Triangle C) (F : Triangle C ⥤ C)
    (U : CategoryTheory.Under T) :
    ((projectionToUnder T F).obj U).right = F.obj U.right := rfl

/-- The structural arrow of `projectionToUnder` is the image of the original structural arrow. -/
@[simp]
theorem projectionToUnder_obj_hom (T : Triangle C) (F : Triangle C ⥤ C)
    (U : CategoryTheory.Under T) :
    ((projectionToUnder T F).obj U).hom = F.map U.hom := rfl

/-- On morphisms, `projectionToUnder` applies the projection functor to the right component. -/
@[simp]
theorem projectionToUnder_map_right (T : Triangle C) (F : Triangle C ⥤ C)
    {U V : CategoryTheory.Under T} (f : U ⟶ V) :
    ((projectionToUnder T F).map f).right = F.map f.right := rfl

/-- A triangle projection gives a functor from triangle denominators to ordinary denominators
whenever it sends the three-component condition to `W`. -/
def projection (W : MorphismProperty C) (T : Triangle C) (F : Triangle C ⥤ C)
    (hF : ∀ U : CategoryTheory.Under T, objectProperty W T U → W (F.map U.hom)) :
    TriangleDenominator W T ⥤ MorphismProperty.Under W ⊤ (F.obj T) :=
  Comma.lift
    ((objectProperty W T).ι ⋙ projectionToUnder T F)
    (fun U ↦ hF U.obj U.property)
    (fun {_ _} f ↦ MorphismProperty.top_apply f)
    (fun {_ _} f ↦ MorphismProperty.top_apply f)

/-- The projected denominator has the projected structural arrow. -/
@[simp]
theorem projection_obj_hom (W : MorphismProperty C) (T : Triangle C)
    (F : Triangle C ⥤ C)
    (hF : ∀ U : CategoryTheory.Under T, objectProperty W T U → W (F.map U.hom))
    (U : TriangleDenominator W T) :
    ((projection W T F hF).obj U).hom = F.map U.obj.hom := rfl

/-- The projected denominator has the projected target object. -/
@[simp]
theorem projection_obj_right (W : MorphismProperty C) (T : Triangle C)
    (F : Triangle C ⥤ C)
    (hF : ∀ U : CategoryTheory.Under T, objectProperty W T U → W (F.map U.hom))
    (U : TriangleDenominator W T) :
    ((projection W T F hF).obj U).right = F.obj U.obj.right := rfl

/-- On morphisms, a denominator projection applies the triangle projection to the underlying
right component. -/
@[simp]
theorem projection_map_right (W : MorphismProperty C) (T : Triangle C)
    (F : Triangle C ⥤ C)
    (hF : ∀ U : CategoryTheory.Under T, objectProperty W T U → W (F.map U.hom))
    {U V : TriangleDenominator W T} (f : U ⟶ V) :
    ((projection W T F hF).map f).right = F.map f.hom.right := rfl

/-- The first-vertex projection from triangle denominators to denominators under `T.obj₁`. -/
@[stacks 05R9 "first projection from triangle denominators"]
def projection₁ (W : MorphismProperty C) (T : Triangle C) :
    TriangleDenominator W T ⥤ MorphismProperty.Under W ⊤ T.obj₁ :=
  projection W T Triangle.π₁ (fun _ hU ↦ hom₁_mem_of_property W T hU)

/-- The second-vertex projection from triangle denominators to denominators under `T.obj₂`. -/
@[stacks 05R9 "second projection from triangle denominators"]
def projection₂ (W : MorphismProperty C) (T : Triangle C) :
    TriangleDenominator W T ⥤ MorphismProperty.Under W ⊤ T.obj₂ :=
  projection W T Triangle.π₂ (fun _ hU ↦ hom₂_mem_of_property W T hU)

/-- The third-vertex projection from triangle denominators to denominators under `T.obj₃`. -/
@[stacks 05R9 "third projection from triangle denominators"]
def projection₃ (W : MorphismProperty C) (T : Triangle C) :
    TriangleDenominator W T ⥤ MorphismProperty.Under W ⊤ T.obj₃ :=
  projection W T Triangle.π₃ (fun _ hU ↦ hom₃_mem_of_property W T hU)

/-- The structural arrow of the first projection is the first component. -/
@[simp]
theorem projection₁_obj_hom (W : MorphismProperty C) (T : Triangle C)
    (U : TriangleDenominator W T) :
    ((projection₁ W T).obj U).hom = U.obj.hom.hom₁ := rfl

/-- The structural arrow of the second projection is the second component. -/
@[simp]
theorem projection₂_obj_hom (W : MorphismProperty C) (T : Triangle C)
    (U : TriangleDenominator W T) :
    ((projection₂ W T).obj U).hom = U.obj.hom.hom₂ := rfl

/-- The structural arrow of the third projection is the third component. -/
@[simp]
theorem projection₃_obj_hom (W : MorphismProperty C) (T : Triangle C)
    (U : TriangleDenominator W T) :
    ((projection₃ W T).obj U).hom = U.obj.hom.hom₃ := rfl

/-- On morphisms, the first projection remembers the first component. -/
@[simp]
theorem projection₁_map_right (W : MorphismProperty C) (T : Triangle C)
    {U V : TriangleDenominator W T} (f : U ⟶ V) :
    ((projection₁ W T).map f).right = f.hom.right.hom₁ := rfl

/-- On morphisms, the second projection remembers the second component. -/
@[simp]
theorem projection₂_map_right (W : MorphismProperty C) (T : Triangle C)
    {U V : TriangleDenominator W T} (f : U ⟶ V) :
    ((projection₂ W T).map f).right = f.hom.right.hom₂ := rfl

/-- On morphisms, the third projection remembers the third component. -/
@[simp]
theorem projection₃_map_right (W : MorphismProperty C) (T : Triangle C)
    {U V : TriangleDenominator W T} (f : U ⟶ V) :
    ((projection₃ W T).map f).right = f.hom.right.hom₃ := rfl

/-- The identity arrow of a distinguished triangle satisfies the triangle-denominator object
property for every morphism property containing identities. -/
theorem identity_mem (W : MorphismProperty C) [W.ContainsIdentities] (T : Triangle C)
    (hT : T ∈ distTriang C) :
    objectProperty W T (CategoryTheory.Under.mk (𝟙 T)) :=
  ⟨hT, W.id_mem T.obj₁, W.id_mem T.obj₂, W.id_mem T.obj₃⟩

/-- The identity arrow of a distinguished triangle, regarded as a canonical triangle
denominator. -/
def identity (W : MorphismProperty C) [W.ContainsIdentities] (T : Triangle C)
    (hT : T ∈ distTriang C) : TriangleDenominator W T :=
  ⟨CategoryTheory.Under.mk (𝟙 T), identity_mem W T hT⟩

end TriangleDenominator
end CategoryTheory.MorphismProperty
