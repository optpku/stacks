module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Left
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Right

@[expose] public section

/-!
# Isomorphism Transport for Pointwise Derived Values

Pointwise derived values are functorial whenever the values at the relevant objects exist.  This
leaf packages the maps induced by an isomorphism of source objects as an isomorphism of derived
values.  The construction is local: it does not require a globally defined derived functor.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)

/-- The maps on pointwise right-derived values induced by the two legs of an isomorphism are
mutually inverse. -/
@[stacks 05SA "right-derived value isomorphism, hom-inv"]
theorem Functor.RightDerived.Value.mapIso_hom_inv_id {X Y : D} (e : X ≅ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y] :
    CategoryTheory.Functor.RightDerived.Value.map F S e.hom ≫ CategoryTheory.Functor.RightDerived.Value.map F S e.inv =
      𝟙 (CategoryTheory.Functor.RightDerived.Value.obj F S X) := sorry

/-- The maps on pointwise right-derived values induced by the inverse and forward legs of an
isomorphism are mutually inverse. -/
@[stacks 05SA "right-derived value isomorphism, inv-hom"]
theorem Functor.RightDerived.Value.mapIso_inv_hom_id {X Y : D} (e : X ≅ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y] :
    CategoryTheory.Functor.RightDerived.Value.map F S e.inv ≫ CategoryTheory.Functor.RightDerived.Value.map F S e.hom =
      𝟙 (CategoryTheory.Functor.RightDerived.Value.obj F S Y) := sorry

/-- An isomorphism of source objects induces an isomorphism of pointwise right-derived values
whenever both values exist. -/
@[stacks 05SA "right-derived value transport along an isomorphism"]
noncomputable def Functor.RightDerived.Value.mapIso {X Y : D} (e : X ≅ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y] :
    CategoryTheory.Functor.RightDerived.Value.obj F S X ≅ CategoryTheory.Functor.RightDerived.Value.obj F S Y where
  hom := CategoryTheory.Functor.RightDerived.Value.map F S e.hom
  inv := CategoryTheory.Functor.RightDerived.Value.map F S e.inv
  hom_inv_id := Functor.RightDerived.Value.mapIso_hom_inv_id F S e
  inv_hom_id := Functor.RightDerived.Value.mapIso_inv_hom_id F S e

/-- The forward leg of right-derived transport along an isomorphism is the canonical pointwise
value map. -/
@[simp, stacks 05SA "right-derived value isomorphism, hom"]
theorem Functor.RightDerived.Value.mapIso_hom {X Y : D} (e : X ≅ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y] :
    (Functor.RightDerived.Value.mapIso F S e).hom = CategoryTheory.Functor.RightDerived.Value.map F S e.hom := sorry

/-- The inverse leg of right-derived transport along an isomorphism is the canonical pointwise
value map induced by the inverse source morphism. -/
@[simp, stacks 05SA "right-derived value isomorphism, inv"]
theorem Functor.RightDerived.Value.mapIso_inv {X Y : D} (e : X ≅ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y] :
    (Functor.RightDerived.Value.mapIso F S e).inv = CategoryTheory.Functor.RightDerived.Value.map F S e.inv := sorry

/-- Right-derived transport along the identity isomorphism is the identity isomorphism. -/
@[simp, stacks 05SA "right-derived value transport of an identity"]
theorem Functor.RightDerived.Value.mapIso_refl (X : D)
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    Functor.RightDerived.Value.mapIso F S (Iso.refl X) = Iso.refl _ := sorry

/-- Right-derived transport along an inverse isomorphism is the inverse transport. -/
@[simp, stacks 05SA "right-derived value transport of an inverse"]
theorem Functor.RightDerived.Value.mapIso_symm {X Y : D} (e : X ≅ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y] :
    Functor.RightDerived.Value.mapIso F S e.symm =
      (Functor.RightDerived.Value.mapIso F S e).symm := sorry

/-- Right-derived transport preserves composition of source isomorphisms. -/
@[simp, stacks 05SA "right-derived value transport of a composite"]
theorem Functor.RightDerived.Value.mapIso_trans {X Y Z : D} (e : X ≅ Y) (e' : Y ≅ Z)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y]
    [F.HasPointwiseRightDerivedFunctorAt S Z] :
    Functor.RightDerived.Value.mapIso F S (e.trans e') =
      (Functor.RightDerived.Value.mapIso F S e).trans
        (Functor.RightDerived.Value.mapIso F S e') := sorry

/-- The maps on pointwise left-derived values induced by the two legs of an isomorphism are
mutually inverse. -/
@[stacks 05SA "left-derived value isomorphism, hom-inv"]
theorem Functor.LeftDerived.Value.mapIso_hom_inv_id {X Y : D} (e : X ≅ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    CategoryTheory.Functor.LeftDerived.Value.map F S e.hom ≫ CategoryTheory.Functor.LeftDerived.Value.map F S e.inv =
      𝟙 (CategoryTheory.Functor.LeftDerived.Value.obj F S X) := sorry

/-- The maps on pointwise left-derived values induced by the inverse and forward legs of an
isomorphism are mutually inverse. -/
@[stacks 05SA "left-derived value isomorphism, inv-hom"]
theorem Functor.LeftDerived.Value.mapIso_inv_hom_id {X Y : D} (e : X ≅ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    CategoryTheory.Functor.LeftDerived.Value.map F S e.inv ≫ CategoryTheory.Functor.LeftDerived.Value.map F S e.hom =
      𝟙 (CategoryTheory.Functor.LeftDerived.Value.obj F S Y) := sorry

/-- An isomorphism of source objects induces an isomorphism of pointwise left-derived values
whenever both values exist. -/
@[stacks 05SA "left-derived value transport along an isomorphism"]
noncomputable def Functor.LeftDerived.Value.mapIso {X Y : D} (e : X ≅ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    CategoryTheory.Functor.LeftDerived.Value.obj F S X ≅ CategoryTheory.Functor.LeftDerived.Value.obj F S Y where
  hom := CategoryTheory.Functor.LeftDerived.Value.map F S e.hom
  inv := CategoryTheory.Functor.LeftDerived.Value.map F S e.inv
  hom_inv_id := Functor.LeftDerived.Value.mapIso_hom_inv_id F S e
  inv_hom_id := Functor.LeftDerived.Value.mapIso_inv_hom_id F S e

/-- The forward leg of left-derived transport along an isomorphism is the canonical pointwise
value map. -/
@[simp, stacks 05SA "left-derived value isomorphism, hom"]
theorem Functor.LeftDerived.Value.mapIso_hom {X Y : D} (e : X ≅ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    (Functor.LeftDerived.Value.mapIso F S e).hom = CategoryTheory.Functor.LeftDerived.Value.map F S e.hom := sorry

/-- The inverse leg of left-derived transport along an isomorphism is the canonical pointwise
value map induced by the inverse source morphism. -/
@[simp, stacks 05SA "left-derived value isomorphism, inv"]
theorem Functor.LeftDerived.Value.mapIso_inv {X Y : D} (e : X ≅ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    (Functor.LeftDerived.Value.mapIso F S e).inv = CategoryTheory.Functor.LeftDerived.Value.map F S e.inv := sorry

/-- Left-derived transport along the identity isomorphism is the identity isomorphism. -/
@[simp, stacks 05SA "left-derived value transport of an identity"]
theorem Functor.LeftDerived.Value.mapIso_refl (X : D)
    [F.HasPointwiseLeftDerivedFunctorAt S X] :
    Functor.LeftDerived.Value.mapIso F S (Iso.refl X) = Iso.refl _ := sorry

/-- Left-derived transport along an inverse isomorphism is the inverse transport. -/
@[simp, stacks 05SA "left-derived value transport of an inverse"]
theorem Functor.LeftDerived.Value.mapIso_symm {X Y : D} (e : X ≅ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    Functor.LeftDerived.Value.mapIso F S e.symm =
      (Functor.LeftDerived.Value.mapIso F S e).symm := sorry

/-- Left-derived transport preserves composition of source isomorphisms. -/
@[simp, stacks 05SA "left-derived value transport of a composite"]
theorem Functor.LeftDerived.Value.mapIso_trans {X Y Z : D} (e : X ≅ Y) (e' : Y ≅ Z)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y]
    [F.HasPointwiseLeftDerivedFunctorAt S Z] :
    Functor.LeftDerived.Value.mapIso F S (e.trans e') =
      (Functor.LeftDerived.Value.mapIso F S e).trans
        (Functor.LeftDerived.Value.mapIso F S e') := sorry



end CategoryTheory
