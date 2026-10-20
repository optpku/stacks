module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Triangle.Construction
public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Shift.Right
public import ReasLib.CategoryTheory.ObjectProperty.Triangle

@[expose] public section

/-!
# Morphisms of Right-Derived Value Triangles

A morphism of source triangles induces a componentwise morphism between their canonical
pointwise right-derived value triangles.  The three square lemmas are exposed independently so
applications can rewrite one edge without unfolding the bundled triangle morphism.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open MorphismProperty Pretriangulated

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasShift D ℤ] [HasShift D' ℤ]
  (F : D ⥤ D') (S : MorphismProperty D)
  [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]

section Map

variable {T₁ T₂ : Triangle D}
  [F.HasPointwiseRightDerivedFunctorAt S T₁.obj₁]
  [F.HasPointwiseRightDerivedFunctorAt S T₁.obj₂]
  [F.HasPointwiseRightDerivedFunctorAt S T₁.obj₃]
  [F.HasPointwiseRightDerivedFunctorAt S T₂.obj₁]
  [F.HasPointwiseRightDerivedFunctorAt S T₂.obj₂]
  [F.HasPointwiseRightDerivedFunctorAt S T₂.obj₃]

/-- The first square of the componentwise map between right-derived value triangles commutes. -/
@[reassoc]
theorem Functor.RightDerived.Value.Triangle.map.comm₁ (f : T₁ ⟶ T₂) :
    (Functor.RightDerived.Value.triangle F S T₁).mor₁ ≫ CategoryTheory.Functor.RightDerived.Value.map F S f.hom₂ =
      CategoryTheory.Functor.RightDerived.Value.map F S f.hom₁ ≫ (Functor.RightDerived.Value.triangle F S T₂).mor₁ := sorry

/-- The second square of the componentwise map between right-derived value triangles commutes. -/
@[reassoc]
theorem Functor.RightDerived.Value.Triangle.map.comm₂ (f : T₁ ⟶ T₂) :
    (Functor.RightDerived.Value.triangle F S T₁).mor₂ ≫ CategoryTheory.Functor.RightDerived.Value.map F S f.hom₃ =
      CategoryTheory.Functor.RightDerived.Value.map F S f.hom₂ ≫ (Functor.RightDerived.Value.triangle F S T₂).mor₂ := sorry

/-- The third square of the componentwise map between right-derived value triangles commutes,
including the canonical shift comparison on the connecting edge. -/
@[reassoc]
theorem Functor.RightDerived.Value.Triangle.map.comm₃ (f : T₁ ⟶ T₂) :
    (Functor.RightDerived.Value.triangle F S T₁).mor₃ ≫
        (CategoryTheory.Functor.RightDerived.Value.map F S f.hom₁)⟦(1 : ℤ)⟧' =
      CategoryTheory.Functor.RightDerived.Value.map F S f.hom₃ ≫
        (Functor.RightDerived.Value.triangle F S T₂).mor₃ := sorry

/-- Stacks 05SC: the componentwise pointwise right-derived maps form a morphism between the
canonical right-derived value triangles. -/
@[stacks 05SC "functoriality of the right-derived value triangle"]
noncomputable def Functor.RightDerived.Value.Triangle.map (f : T₁ ⟶ T₂) :
    Functor.RightDerived.Value.triangle F S T₁ ⟶ Functor.RightDerived.Value.triangle F S T₂ where
  hom₁ := CategoryTheory.Functor.RightDerived.Value.map F S f.hom₁
  hom₂ := CategoryTheory.Functor.RightDerived.Value.map F S f.hom₂
  hom₃ := CategoryTheory.Functor.RightDerived.Value.map F S f.hom₃
  comm₁ := Functor.RightDerived.Value.Triangle.map.comm₁ F S f
  comm₂ := Functor.RightDerived.Value.Triangle.map.comm₂ F S f
  comm₃ := Functor.RightDerived.Value.Triangle.map.comm₃ F S f

/-- The first component of `Functor.RightDerived.Value.Triangle.map` is the pointwise right-derived map. -/
@[simp]
theorem Functor.RightDerived.Value.Triangle.map.hom₁ (f : T₁ ⟶ T₂) :
    (Functor.RightDerived.Value.Triangle.map F S f).hom₁ = CategoryTheory.Functor.RightDerived.Value.map F S f.hom₁ := sorry

/-- The second component of `Functor.RightDerived.Value.Triangle.map` is the pointwise right-derived map. -/
@[simp]
theorem Functor.RightDerived.Value.Triangle.map.hom₂ (f : T₁ ⟶ T₂) :
    (Functor.RightDerived.Value.Triangle.map F S f).hom₂ = CategoryTheory.Functor.RightDerived.Value.map F S f.hom₂ := sorry

/-- The third component of `Functor.RightDerived.Value.Triangle.map` is the pointwise right-derived map. -/
@[simp]
theorem Functor.RightDerived.Value.Triangle.map.hom₃ (f : T₁ ⟶ T₂) :
    (Functor.RightDerived.Value.Triangle.map F S f).hom₃ = CategoryTheory.Functor.RightDerived.Value.map F S f.hom₃ := sorry

end Map

section Functoriality

/-- The right-derived value triangle map sends an identity triangle morphism to an identity. -/
@[simp]
theorem Functor.RightDerived.Value.Triangle.map.id
    (T : Triangle D)
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₃] :
    Functor.RightDerived.Value.Triangle.map F S (𝟙 T) = 𝟙 (Functor.RightDerived.Value.triangle F S T) := sorry

/-- The right-derived value triangle map preserves composition of triangle morphisms. -/
@[simp]
theorem Functor.RightDerived.Value.Triangle.map.comp
    {T₁ T₂ T₃ : Triangle D}
    [F.HasPointwiseRightDerivedFunctorAt S T₁.obj₁]
    [F.HasPointwiseRightDerivedFunctorAt S T₁.obj₂]
    [F.HasPointwiseRightDerivedFunctorAt S T₁.obj₃]
    [F.HasPointwiseRightDerivedFunctorAt S T₂.obj₁]
    [F.HasPointwiseRightDerivedFunctorAt S T₂.obj₂]
    [F.HasPointwiseRightDerivedFunctorAt S T₂.obj₃]
    [F.HasPointwiseRightDerivedFunctorAt S T₃.obj₁]
    [F.HasPointwiseRightDerivedFunctorAt S T₃.obj₂]
    [F.HasPointwiseRightDerivedFunctorAt S T₃.obj₃]
    (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    Functor.RightDerived.Value.Triangle.map F S (f ≫ g) =
      Functor.RightDerived.Value.Triangle.map F S f ≫ Functor.RightDerived.Value.Triangle.map F S g := sorry

end Functoriality

namespace Functor.RightDerived.Value.Triangle

open ObjectProperty

/-- The object property of source triangles at whose three vertices the pointwise right-derived
value exists. -/
@[stacks 05SC "domain of the pointwise right-derived value triangle"]
abbrev objects : ObjectProperty (Triangle D) :=
  (Functor.RightDerived.Definedness.property F S).triangle

/-- The full category of triangles on which all three pointwise right-derived values exist. -/
@[stacks 05SC "domain category of the pointwise right-derived value triangle"]
abbrev Domain := (objects F S).FullSubcategory

/-- The first-vertex projection from the right-derived value-triangle domain to the ordinary
right-derived domain. -/
abbrev π₁ : Domain F S ⥤ Functor.RightDerived.Definedness.Domain F S :=
  ObjectProperty.triangle.π₁ (Functor.RightDerived.Definedness.property F S)

/-- The second-vertex projection from the right-derived value-triangle domain to the ordinary
right-derived domain. -/
abbrev π₂ : Domain F S ⥤ Functor.RightDerived.Definedness.Domain F S :=
  ObjectProperty.triangle.π₂ (Functor.RightDerived.Definedness.property F S)

/-- The third-vertex projection from the right-derived value-triangle domain to the ordinary
right-derived domain. -/
abbrev π₃ : Domain F S ⥤ Functor.RightDerived.Definedness.Domain F S :=
  ObjectProperty.triangle.π₃ (Functor.RightDerived.Definedness.property F S)

/-- Membership in `Functor.RightDerived.Value.Triangle.Domain` supplies pointwise right-derived
existence at the first vertex. -/
instance Domain.hasPointwiseAtObj₁ (T : Domain F S) :
    F.HasPointwiseRightDerivedFunctorAt S T.obj.obj₁ := (π₁ F S).obj T |>.property

/-- Membership in `Functor.RightDerived.Value.Triangle.Domain` supplies pointwise right-derived
existence at the second vertex. -/
instance Domain.hasPointwiseAtObj₂ (T : Domain F S) :
    F.HasPointwiseRightDerivedFunctorAt S T.obj.obj₂ := (π₂ F S).obj T |>.property

/-- Membership in `Functor.RightDerived.Value.Triangle.Domain` supplies pointwise right-derived
existence at the third vertex. -/
instance Domain.hasPointwiseAtObj₃ (T : Domain F S) :
    F.HasPointwiseRightDerivedFunctorAt S T.obj.obj₃ := (π₃ F S).obj T |>.property

/-- The pointwise right-derived value construction as a functor from its full triangle domain. -/
@[stacks 05SC "pointwise right-derived functor on triangles"]
noncomputable def functor : Domain F S ⥤ Triangle D' where
  obj T := Functor.RightDerived.Value.triangle F S T.obj
  map f := Functor.RightDerived.Value.Triangle.map F S f.hom
  map_id T := Functor.RightDerived.Value.Triangle.map.id F S T.obj
  map_comp f g := Functor.RightDerived.Value.Triangle.map.comp F S f.hom g.hom

/-- The triangle functor evaluates on objects as `Functor.RightDerived.Value.triangle`. -/
@[simp]
theorem functor.obj (T : Domain F S) :
    (functor F S).obj T = Functor.RightDerived.Value.triangle F S T.obj := sorry

/-- The triangle functor maps a morphism by the bundled componentwise right-derived triangle
map of its underlying source morphism. -/
@[simp, stacks 05SC "pointwise right-derived triangle functor on morphisms"]
theorem functor.map {T₁ T₂ : Domain F S} (f : T₁ ⟶ T₂) :
    (functor F S).map f = Functor.RightDerived.Value.Triangle.map F S f.hom := sorry

/-- The first component of the triangle functor on a morphism is the pointwise right-derived
map of its first component. -/
@[simp]
theorem functor.map_hom₁ {T₁ T₂ : Domain F S} (f : T₁ ⟶ T₂) :
    ((functor F S).map f).hom₁ = CategoryTheory.Functor.RightDerived.Value.map F S f.hom.hom₁ := sorry

/-- The second component of the triangle functor on a morphism is the pointwise right-derived
map of its second component. -/
@[simp]
theorem functor.map_hom₂ {T₁ T₂ : Domain F S} (f : T₁ ⟶ T₂) :
    ((functor F S).map f).hom₂ = CategoryTheory.Functor.RightDerived.Value.map F S f.hom.hom₂ := sorry

/-- The third component of the triangle functor on a morphism is the pointwise right-derived
map of its third component. -/
@[simp]
theorem functor.map_hom₃ {T₁ T₂ : Domain F S} (f : T₁ ⟶ T₂) :
    ((functor F S).map f).hom₃ = CategoryTheory.Functor.RightDerived.Value.map F S f.hom.hom₃ := sorry

end Functor.RightDerived.Value.Triangle

end CategoryTheory
