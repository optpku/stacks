/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Triangle.Construction
public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Shift.Left
public import ReasLib.CategoryTheory.ObjectProperty.Triangle

@[expose] public section

/-!
# Functoriality of Left-Derived Value Triangles

This leaf packages the pointwise left-derived maps induced by a morphism of triangles into a
morphism between the corresponding left-derived value triangles.  The three commutativity
statements are exposed separately so downstream constructions can reuse them without unpacking
the bundled triangle morphism.
-/

open CategoryTheory.MorphismProperty CategoryTheory.Pretriangulated

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasShift D ℤ] [HasShift D' ℤ]
  (F : D ⥤ D') (S : MorphismProperty D)
  [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]

section Map

variable {T₁ T₂ : Triangle D}
  [F.HasPointwiseLeftDerivedFunctorAt S T₁.obj₁]
  [F.HasPointwiseLeftDerivedFunctorAt S T₁.obj₂]
  [F.HasPointwiseLeftDerivedFunctorAt S T₁.obj₃]
  [F.HasPointwiseLeftDerivedFunctorAt S T₂.obj₁]
  [F.HasPointwiseLeftDerivedFunctorAt S T₂.obj₂]
  [F.HasPointwiseLeftDerivedFunctorAt S T₂.obj₃]

/-- The first square induced by applying pointwise left-derived values to a morphism of
triangles commutes. -/
@[reassoc]
theorem Functor.LeftDerived.Value.Triangle.map.comm₁ (f : T₁ ⟶ T₂) :
    (Functor.LeftDerived.Value.triangle F S T₁).mor₁ ≫ CategoryTheory.Functor.LeftDerived.Value.map F S f.hom₂ =
      CategoryTheory.Functor.LeftDerived.Value.map F S f.hom₁ ≫ (Functor.LeftDerived.Value.triangle F S T₂).mor₁ := sorry

/-- The second square induced by applying pointwise left-derived values to a morphism of
triangles commutes. -/
@[reassoc]
theorem Functor.LeftDerived.Value.Triangle.map.comm₂ (f : T₁ ⟶ T₂) :
    (Functor.LeftDerived.Value.triangle F S T₁).mor₂ ≫ CategoryTheory.Functor.LeftDerived.Value.map F S f.hom₃ =
      CategoryTheory.Functor.LeftDerived.Value.map F S f.hom₂ ≫ (Functor.LeftDerived.Value.triangle F S T₂).mor₂ := sorry

/-- The third square induced by applying pointwise left-derived values to a morphism of
triangles commutes, including the canonical comparison with the shift by `1`. -/
@[reassoc]
theorem Functor.LeftDerived.Value.Triangle.map.comm₃ (f : T₁ ⟶ T₂) :
    (Functor.LeftDerived.Value.triangle F S T₁).mor₃ ≫
        (CategoryTheory.Functor.LeftDerived.Value.map F S f.hom₁)⟦(1 : ℤ)⟧' =
      CategoryTheory.Functor.LeftDerived.Value.map F S f.hom₃ ≫ (Functor.LeftDerived.Value.triangle F S T₂).mor₃ := sorry

/-- The morphism of left-derived value triangles induced by a morphism of source triangles. -/
@[stacks 05SC "functoriality of left-derived value triangles"]
noncomputable def Functor.LeftDerived.Value.Triangle.map (f : T₁ ⟶ T₂) :
    Functor.LeftDerived.Value.triangle F S T₁ ⟶ Functor.LeftDerived.Value.triangle F S T₂ where
  hom₁ := CategoryTheory.Functor.LeftDerived.Value.map F S f.hom₁
  hom₂ := CategoryTheory.Functor.LeftDerived.Value.map F S f.hom₂
  hom₃ := CategoryTheory.Functor.LeftDerived.Value.map F S f.hom₃
  comm₁ := Functor.LeftDerived.Value.Triangle.map.comm₁ F S f
  comm₂ := Functor.LeftDerived.Value.Triangle.map.comm₂ F S f
  comm₃ := Functor.LeftDerived.Value.Triangle.map.comm₃ F S f

/-- The first component of `Functor.LeftDerived.Value.Triangle.map` is the pointwise left-derived map of
the first component. -/
@[simp]
theorem Functor.LeftDerived.Value.Triangle.map.hom₁ (f : T₁ ⟶ T₂) :
    (Functor.LeftDerived.Value.Triangle.map F S f).hom₁ = CategoryTheory.Functor.LeftDerived.Value.map F S f.hom₁ := sorry

/-- The second component of `Functor.LeftDerived.Value.Triangle.map` is the pointwise left-derived map of
the second component. -/
@[simp]
theorem Functor.LeftDerived.Value.Triangle.map.hom₂ (f : T₁ ⟶ T₂) :
    (Functor.LeftDerived.Value.Triangle.map F S f).hom₂ = CategoryTheory.Functor.LeftDerived.Value.map F S f.hom₂ := sorry

/-- The third component of `Functor.LeftDerived.Value.Triangle.map` is the pointwise left-derived map of
the third component. -/
@[simp]
theorem Functor.LeftDerived.Value.Triangle.map.hom₃ (f : T₁ ⟶ T₂) :
    (Functor.LeftDerived.Value.Triangle.map F S f).hom₃ = CategoryTheory.Functor.LeftDerived.Value.map F S f.hom₃ := sorry

end Map

/-- The morphism of left-derived value triangles induced by an identity is the identity
triangle morphism. -/
@[simp]
theorem Functor.LeftDerived.Value.Triangle.map.id (T : Triangle D)
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₃] :
    Functor.LeftDerived.Value.Triangle.map F S (𝟙 T) = 𝟙 (Functor.LeftDerived.Value.triangle F S T) := sorry

/-- Morphisms of left-derived value triangles respect composition of source triangle
morphisms. -/
@[simp]
theorem Functor.LeftDerived.Value.Triangle.map.comp
    {T₁ T₂ T₃ : Triangle D}
    [F.HasPointwiseLeftDerivedFunctorAt S T₁.obj₁]
    [F.HasPointwiseLeftDerivedFunctorAt S T₁.obj₂]
    [F.HasPointwiseLeftDerivedFunctorAt S T₁.obj₃]
    [F.HasPointwiseLeftDerivedFunctorAt S T₂.obj₁]
    [F.HasPointwiseLeftDerivedFunctorAt S T₂.obj₂]
    [F.HasPointwiseLeftDerivedFunctorAt S T₂.obj₃]
    [F.HasPointwiseLeftDerivedFunctorAt S T₃.obj₁]
    [F.HasPointwiseLeftDerivedFunctorAt S T₃.obj₂]
    [F.HasPointwiseLeftDerivedFunctorAt S T₃.obj₃]
    (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    Functor.LeftDerived.Value.Triangle.map F S (f ≫ g) =
      Functor.LeftDerived.Value.Triangle.map F S f ≫ Functor.LeftDerived.Value.Triangle.map F S g := sorry

namespace Functor.LeftDerived.Value.Triangle

open ObjectProperty

/-- The object property of source triangles at whose three vertices the pointwise left-derived
value exists. -/
@[stacks 05SC "domain of the pointwise left-derived value triangle"]
abbrev objects : ObjectProperty (Triangle D) :=
  (Functor.LeftDerived.Definedness.property F S).triangle

/-- The full category of triangles on which all three pointwise left-derived values exist. -/
@[stacks 05SC "domain category of the pointwise left-derived value triangle"]
abbrev Domain := (objects F S).FullSubcategory

/-- The first-vertex projection from the left-derived value-triangle domain to the ordinary
left-derived domain. -/
abbrev π₁ : Domain F S ⥤ Functor.LeftDerived.Definedness.Domain F S :=
  ObjectProperty.triangle.π₁ (Functor.LeftDerived.Definedness.property F S)

/-- The second-vertex projection from the left-derived value-triangle domain to the ordinary
left-derived domain. -/
abbrev π₂ : Domain F S ⥤ Functor.LeftDerived.Definedness.Domain F S :=
  ObjectProperty.triangle.π₂ (Functor.LeftDerived.Definedness.property F S)

/-- The third-vertex projection from the left-derived value-triangle domain to the ordinary
left-derived domain. -/
abbrev π₃ : Domain F S ⥤ Functor.LeftDerived.Definedness.Domain F S :=
  ObjectProperty.triangle.π₃ (Functor.LeftDerived.Definedness.property F S)

/-- Membership in `Functor.LeftDerived.Value.Triangle.Domain` supplies pointwise left-derived
existence at the first vertex. -/
instance Domain.hasPointwiseAtObj₁ (T : Domain F S) :
    F.HasPointwiseLeftDerivedFunctorAt S T.obj.obj₁ := (π₁ F S).obj T |>.property

/-- Membership in `Functor.LeftDerived.Value.Triangle.Domain` supplies pointwise left-derived
existence at the second vertex. -/
instance Domain.hasPointwiseAtObj₂ (T : Domain F S) :
    F.HasPointwiseLeftDerivedFunctorAt S T.obj.obj₂ := (π₂ F S).obj T |>.property

/-- Membership in `Functor.LeftDerived.Value.Triangle.Domain` supplies pointwise left-derived
existence at the third vertex. -/
instance Domain.hasPointwiseAtObj₃ (T : Domain F S) :
    F.HasPointwiseLeftDerivedFunctorAt S T.obj.obj₃ := (π₃ F S).obj T |>.property

/-- The pointwise left-derived value construction as a functor from its full triangle domain. -/
@[stacks 05SC "pointwise left-derived functor on triangles"]
noncomputable def functor : Domain F S ⥤ Triangle D' where
  obj T := Functor.LeftDerived.Value.triangle F S T.obj
  map f := Functor.LeftDerived.Value.Triangle.map F S f.hom
  map_id T := Functor.LeftDerived.Value.Triangle.map.id F S T.obj
  map_comp f g := Functor.LeftDerived.Value.Triangle.map.comp F S f.hom g.hom

/-- The triangle functor evaluates on objects as `Functor.LeftDerived.Value.triangle`. -/
@[simp]
theorem functor.obj (T : Domain F S) :
    (functor F S).obj T = Functor.LeftDerived.Value.triangle F S T.obj := sorry

/-- The triangle functor maps a morphism by the bundled componentwise left-derived triangle map
of its underlying source morphism. -/
@[simp, stacks 05SC "pointwise left-derived triangle functor on morphisms"]
theorem functor.map {T₁ T₂ : Domain F S} (f : T₁ ⟶ T₂) :
    (functor F S).map f = Functor.LeftDerived.Value.Triangle.map F S f.hom := sorry

/-- The first component of the triangle functor on a morphism is the pointwise left-derived
map of its first component. -/
@[simp]
theorem functor.map_hom₁ {T₁ T₂ : Domain F S} (f : T₁ ⟶ T₂) :
    ((functor F S).map f).hom₁ = CategoryTheory.Functor.LeftDerived.Value.map F S f.hom.hom₁ := sorry

/-- The second component of the triangle functor on a morphism is the pointwise left-derived
map of its second component. -/
@[simp]
theorem functor.map_hom₂ {T₁ T₂ : Domain F S} (f : T₁ ⟶ T₂) :
    ((functor F S).map f).hom₂ = CategoryTheory.Functor.LeftDerived.Value.map F S f.hom.hom₂ := sorry

/-- The third component of the triangle functor on a morphism is the pointwise left-derived
map of its third component. -/
@[simp]
theorem functor.map_hom₃ {T₁ T₂ : Domain F S} (f : T₁ ⟶ T₂) :
    ((functor F S).map f).hom₃ = CategoryTheory.Functor.LeftDerived.Value.map F S f.hom.hom₃ := sorry

end Functor.LeftDerived.Value.Triangle

end CategoryTheory
