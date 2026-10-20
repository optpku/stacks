/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Definition
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Fibers
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Closure
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.ULift
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# The bicategory of categories cofibered in groupoids

The full subbicategory of `BasedCategory C` on projections `p` with
`Functor.IsFibered.InGroupoids p.op`, together with object constructors, forgetful views, and
the identity/product API.
-/

@[expose] public section

universe u v w vS vB

namespace CategoryTheory

open Bicategory
open ObjectProperty
open BasedFunctor
open BasedCategory
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]

/-- The object property on `BasedCategory C` selecting projections cofibered in groupoids. -/
abbrev BasedCategory.isCofiberedInGroupoids (C : Type u) [Category.{v} C] :
    ObjectProperty (BasedCategory.{vS, w} C) :=
  fun X ↦ Functor.IsFibered.InGroupoids X.p.op

namespace BasedCategory.isCofiberedInGroupoids

/-- Being cofibered in groupoids is invariant under equivalence in `BasedCategory C`. -/
instance isClosedUnderEquivalences (C : Type u) [Category.{v} C] :
    (isCofiberedInGroupoids C).IsClosedUnderEquivalences := sorry

/-- The universe-stable object property of being cofibered in groupoids is closed under the
explicit based pseudo-pullback. -/
instance PseudoPullback.isClosedUnder :
    BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder
      (isCofiberedInGroupoids C :
        ObjectProperty
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)) := sorry

end BasedCategory.isCofiberedInGroupoids

/-- Standard fibres of a category cofibered in groupoids are groupoids. -/
instance Functor.IsFibered.InGroupoids.fiberIsGroupoid_of_cofibered
    {F : Type w} [Category.{vS} F] (p : F ⥤ C)
    [Functor.IsFibered.InGroupoids p.op] (U : C) :
    IsGroupoid (p.Fiber U) := sorry

/-- The universe-down functor of a bundled object-universe lift is cofibered in groupoids. -/
instance Cat.ObjULift.down.op_inGroupoids (C : Type u) [Category.{v} C] :
    Functor.IsFibered.InGroupoids (Cat.ObjULift.down.{u, v, w} C).op := sorry

/-- The universe-down functor of a bundled object- and morphism-universe lift is cofibered
in groupoids. -/
instance Cat.TwoULift.down.op_inGroupoids (C : Type u) [Category.{v} C] :
    Functor.IsFibered.InGroupoids (Cat.TwoULift.down.{u, v, w, vB} C).op := sorry

set_option linter.checkUnivs false in
/-- Categories cofibered in groupoids over `C` form the full induced `2`-category of
`BasedCategory C` cut out by `BasedCategory.isCofiberedInGroupoids`. -/
abbrev CofiberedCategoryOver.Groupoids (C : Type u) [Category.{v} C] :=
  ((BasedCategory.isCofiberedInGroupoids C :
    ObjectProperty (BasedCategory.{vS, w} C))).FullSubbicategory

namespace CofiberedCategoryOver.Groupoids

/-- Build a bundled category cofibered in groupoids over `C` from a functor to `C`. -/
def ofFunctor {S : Type w} [Category.{vS} S] (p : S ⥤ C)
    [h : Functor.IsFibered.InGroupoids p.op] :
    CofiberedCategoryOver.Groupoids C :=
  ⟨BasedCategory.ofFunctor p, h⟩

/-- The underlying based category over `C`. -/
abbrev toBasedCategory (X : CofiberedCategoryOver.Groupoids C) : BasedCategory.{vS, w} C :=
  X.1

/-- The total category of a bundled category cofibered in groupoids over `C`. -/
abbrev total (X : CofiberedCategoryOver.Groupoids C) :=
  X.toBasedCategory.obj

/-- The projection functor of a bundled category cofibered in groupoids over `C`. -/
abbrev p (X : CofiberedCategoryOver.Groupoids C) :=
  X.toBasedCategory.p

/-- The canonical projection of `ofFunctor p` is the supplied functor `p`. -/
@[simp]
theorem ofFunctor_p {S : Type w} [Category.{vS} S] (p : S ⥤ C)
    [Functor.IsFibered.InGroupoids p.op] : (ofFunctor p).p = p := rfl

/-- The total category of `ofFunctor p` is the source category of `p`. -/
@[simp]
theorem ofFunctor.total {S : Type w} [Category.{vS} S] (p : S ⥤ C)
    [Functor.IsFibered.InGroupoids p.op] : (ofFunctor p).total = S := sorry

/-- A based category lies in `CofiberedCategoryOver.Groupoids C` precisely when its
opposite projection is fibred in groupoids. -/
theorem spec {X : BasedCategory.{vS, w} C} :
    isCofiberedInGroupoids C X ↔ Functor.IsFibered.InGroupoids X.p.op := Iff.rfl

/-- The projection of a bundled category cofibered in groupoids is cofibered in groupoids. -/
instance projectionInGroupoids (X : CofiberedCategoryOver.Groupoids C) :
    Functor.IsFibered.InGroupoids X.p.op := X.property

/-- Categories cofibered in groupoids form a `(2,1)`-category. -/
instance locallyGroupoid : IsLocallyGroupoid (CofiberedCategoryOver.Groupoids C) := sorry

/-- Canonical coercion to the ambient based-category API. -/
instance coeBasedCategory : CoeOut (CofiberedCategoryOver.Groupoids C) (BasedCategory.{vS, w} C) where
  coe X := X.toBasedCategory

variable (C) in
/-- The canonical strict inclusion into the ambient `2`-category of based categories. -/
abbrev toBased : StrictPseudofunctor
    (CofiberedCategoryOver.Groupoids C) (BasedCategory.{vS, w} C) :=
  ObjectProperty.FullSubbicategory.ι _

variable {X Y : CofiberedCategoryOver.Groupoids C}

/-- The underlying based functor of a morphism of categories cofibered in groupoids over `C`. -/
abbrev toBasedFunctor (F : X ⟶ Y) : X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  F.hom

/-- The underlying functor between the total categories. -/
abbrev toFunctor (F : X ⟶ Y) : X.total ⥤ Y.total :=
  toBasedFunctor F |>.toFunctor

/-- The compatibility of the underlying functor with the base projections. -/
abbrev comm (F : X ⟶ Y) : toFunctor F ⋙ Y.p = X.p :=
  toBasedFunctor F |>.w

/-- The based-functor view of the identity morphism is the identity based functor. -/
@[simp]
theorem toBasedFunctor.id (X : CofiberedCategoryOver.Groupoids C) :
    toBasedFunctor (𝟙 X) = 𝟙 X.toBasedCategory := sorry

/-- The based-functor view preserves composition. -/
@[simp]
theorem toBasedFunctor.comp
    {Z : CofiberedCategoryOver.Groupoids C} (F : X ⟶ Y) (G : Y ⟶ Z) :
    toBasedFunctor (F ≫ G) =
      BasedFunctor.comp (toBasedFunctor F) (toBasedFunctor G) := sorry

/-- The total-category functor underlying the identity morphism is the identity functor. -/
@[simp]
theorem toFunctor.id (X : CofiberedCategoryOver.Groupoids C) :
    toFunctor (𝟙 X) = 𝟭 X.total := sorry

/-- Passing to total-category functors preserves composition. -/
@[simp]
theorem toFunctor.comp
    {Z : CofiberedCategoryOver.Groupoids C} (F : X ⟶ Y) (G : Y ⟶ Z) :
    toFunctor (F ≫ G) = toFunctor F ⋙ toFunctor G := sorry

/-- Build a morphism of categories cofibered in groupoids from a based functor over `C`. -/
def ofBasedFunctor
    (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    X ⟶ Y :=
  Bicategory.InducedBicategory.mkHom G

/-- Projecting a morphism built by `ofBasedFunctor` recovers the supplied based functor. -/
@[simp]
theorem ofBasedFunctor_toBasedFunctor
    (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    toBasedFunctor (ofBasedFunctor G) = G := rfl

/-- Reconstructing a morphism from its underlying based functor recovers the original morphism. -/
@[simp]
theorem toBasedFunctor_ofBasedFunctor (F : X ⟶ Y) :
    ofBasedFunctor (toBasedFunctor F) = F := rfl

/-- The underlying based natural transformation of a `2`-morphism. -/
abbrev toBasedNatTrans {F G : X ⟶ Y} (eta : F ⟶ G) :
    toBasedFunctor F ⟶ toBasedFunctor G :=
  eta.hom

/-- Build a `2`-morphism from a based natural transformation. -/
def ofBasedNatTrans {F G : X ⟶ Y}
    (eta : toBasedFunctor F ⟶ toBasedFunctor G) : F ⟶ G :=
  Bicategory.InducedBicategory.mkHom₂ eta

/-- Projecting a `2`-morphism built by `ofBasedNatTrans` recovers the supplied transformation. -/
@[simp]
theorem ofBasedNatTrans_toBasedNatTrans {F G : X ⟶ Y}
    (eta : toBasedFunctor F ⟶ toBasedFunctor G) :
    toBasedNatTrans (ofBasedNatTrans eta) = eta := rfl

/-- Rebundling the underlying based natural transformation recovers the original `2`-morphism. -/
@[simp]
theorem toBasedNatTrans_ofBasedNatTrans {F G : X ⟶ Y} (eta : F ⟶ G) :
    ofBasedNatTrans (toBasedNatTrans eta) = eta := rfl

/-- The ordinary natural transformation on total categories underlying a `2`-morphism. -/
abbrev toNatTrans {F G : X ⟶ Y} (eta : F ⟶ G) :
    toFunctor F ⟶ toFunctor G :=
  (toBasedNatTrans eta).toNatTrans

/-- Every `2`-cell between cofibered morphisms lies over the identity of the source base object. -/
theorem TwoCell.app.isHomLiftId
    {F G : X ⟶ Y} (eta : F ⟶ G) (a : X.total) :
    Functor.IsHomLift Y.p (𝟙 (X.p.obj a)) ((toNatTrans eta).app a) := sorry

/-- The canonical based functor from a cofibered category to the identity based category. -/
def toBase (X : CofiberedCategoryOver.Groupoids C) :
    X.toBasedCategory ⥤ᵇ BasedCategory.ofFunctor (𝟭 C) :=
  BasedCategory.toBase X.toBasedCategory

variable (C) in
/-- The identity cofibered category on `C`, represented at the universe-closed owner used by
canonical two-fibre products, with independently resized object and morphism universes. -/
def base :
    CofiberedCategoryOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} C :=
  ofFunctor (Cat.TwoULift.down.{u, v, max w (max v vB), vB} C)

variable (C) in
/-- The canonical section of the universe-resized identity cofibered category. -/
def baseSection : C ⥤ (base.{u, v, w, vB} C).total :=
  Cat.TwoULift.up.{u, v, max w (max v vB), vB} C

/-- The identity-fibration section followed by the identity-fibration projection is the identity
on `C`. -/
theorem baseSection.comp_projection :
    baseSection.{u, v, w, vB} C ⋙ (base.{u, v, w, vB} C).p = 𝟭 C := sorry

/-- The equality over `C` used by the canonical morphism from `X` to `base C`. -/
theorem baseProjection.comm
    (X : CofiberedCategoryOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} C) :
    (X.p ⋙ baseSection.{u, v, w, vB} C) ⋙ (base.{u, v, w, vB} C).p = X.p := sorry

/-- The canonical `1`-morphism from a category cofibered in groupoids to the universe-resized
identity cofibered category. -/
def baseProjection
    (X : CofiberedCategoryOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} C) :
    X ⟶ base.{u, v, w, vB} C :=
  ofBasedFunctor
    (BasedFunctor.ofFunctor (X.p ⋙ baseSection.{u, v, w, vB} C) (baseProjection.comm X))

/-- The product of two categories cofibered in groupoids is their `2`-fibre product over the
identity cofibered category. -/
noncomputable def product
    (X Y : CofiberedCategoryOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} C) :
    CofiberedCategoryOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} C :=
  TwoFibreProduct.apex (baseProjection X) (baseProjection Y)

/-- The product is the chosen two-fibre-product apex over the identity cofibered category. -/
theorem product_eq_apex
    (X Y : CofiberedCategoryOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} C) :
    product X Y = TwoFibreProduct.apex (baseProjection X) (baseProjection Y) := sorry

end CofiberedCategoryOver.Groupoids

end CategoryTheory
