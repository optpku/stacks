/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Definition
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# Categories cofibered in groupoids

The full subbicategory of `BasedCategory C` whose projections are cofibered in groupoids,
i.e. whose opposite functors are fibred in groupoids, together with object constructors
and based `1`- and `2`-cell bridges.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory ObjectProperty BasedFunctor BasedCategory
open scoped BasedFunctor Bicategory

/-- The object property selecting based categories cofibered in groupoids over `C`.
This is the dual of `BasedCategory.isFiberedInGroupoids`: a projection `X.p` is
cofibered in groupoids precisely when `X.p.op` is fibred in groupoids. -/
abbrev BasedCategory.isCofiberedInGroupoids (C : Type u) [Category.{v} C] :
    ObjectProperty (BasedCategory.{vS, w} C) :=
  fun X ↦ Functor.IsFibered.InGroupoids X.p.op

set_option linter.checkUnivs false in
/-- The `2`-category of categories cofibered in groupoids over `C`, as the full
subbicategory of `BasedCategory C` cut out by `BasedCategory.isCofiberedInGroupoids`. -/
abbrev CofiberedCategoryOver.Groupoids (C : Type u) [Category.{v} C] :=
  ((BasedCategory.isCofiberedInGroupoids C :
    ObjectProperty (BasedCategory.{vS, w} C))).FullSubbicategory

variable {C : Type u} [Category.{v} C]

namespace CofiberedCategoryOver.Groupoids

/-- Build a bundled category cofibered in groupoids over `C` from a functor to `C`. -/
def ofFunctor {S : Type w} [Category.{vS} S] (p : S ⥤ C)
    [h : Functor.IsFibered.InGroupoids p.op] :
    CofiberedCategoryOver.Groupoids C :=
  ⟨BasedCategory.ofFunctor p, h⟩

/-- The underlying based category over `C`. -/
abbrev toBasedCategory (X : CofiberedCategoryOver.Groupoids C) :
    BasedCategory.{vS, w} C :=
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

/-- A based category lies in `CofiberedCategoryOver.Groupoids C` precisely when its
opposite projection is fibred in groupoids. -/
theorem spec {X : BasedCategory.{vS, w} C} :
    isCofiberedInGroupoids C X ↔ Functor.IsFibered.InGroupoids X.p.op := Iff.rfl

/-- The projection of a bundled category cofibered in groupoids is cofibered in groupoids. -/
instance projectionInGroupoids (X : CofiberedCategoryOver.Groupoids C) :
    Functor.IsFibered.InGroupoids X.p.op :=
  X.property

variable (C) in
/-- The canonical strict inclusion into the ambient `2`-category of based categories. -/
abbrev toBased : StrictPseudofunctor
    (CofiberedCategoryOver.Groupoids C) (BasedCategory.{vS, w} C) :=
  ObjectProperty.FullSubbicategory.ι _

variable {X Y : CofiberedCategoryOver.Groupoids C}

/-- The underlying based functor of a morphism of categories cofibered in groupoids. -/
abbrev toBasedFunctor (F : X ⟶ Y) : X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  F.hom

/-- Build a morphism of categories cofibered in groupoids from a based functor over `C`. -/
def ofBasedFunctor (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) : X ⟶ Y :=
  Bicategory.InducedBicategory.mkHom G

/-- Projecting a morphism built by `ofBasedFunctor` recovers the supplied based functor. -/
@[simp]
theorem ofBasedFunctor_toBasedFunctor (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    toBasedFunctor (ofBasedFunctor G) = G := rfl

/-- Reconstructing a cofibered morphism from its underlying based functor recovers it. -/
@[simp]
theorem toBasedFunctor_ofBasedFunctor (F : X ⟶ Y) :
    ofBasedFunctor (toBasedFunctor F) = F := rfl

/-- The underlying based natural transformation of a `2`-morphism of cofibered morphisms. -/
abbrev toBasedNatTrans {F G : X ⟶ Y} (eta : F ⟶ G) :
    toBasedFunctor F ⟶ toBasedFunctor G :=
  eta.hom

/-- Build a `2`-morphism of cofibered morphisms from a based natural transformation. -/
def ofBasedNatTrans {F G : X ⟶ Y}
    (eta : toBasedFunctor F ⟶ toBasedFunctor G) : F ⟶ G :=
  Bicategory.InducedBicategory.mkHom₂ eta

/-- Projecting a `2`-morphism built by `ofBasedNatTrans` recovers the supplied based
natural transformation. -/
@[simp]
theorem ofBasedNatTrans_toBasedNatTrans {F G : X ⟶ Y}
    (eta : toBasedFunctor F ⟶ toBasedFunctor G) :
    toBasedNatTrans (ofBasedNatTrans eta) = eta := rfl

/-- Rebundling the underlying based natural transformation recovers the original `2`-morphism. -/
@[simp]
theorem toBasedNatTrans_ofBasedNatTrans {F G : X ⟶ Y} (eta : F ⟶ G) :
    ofBasedNatTrans (toBasedNatTrans eta) = eta := rfl

end CofiberedCategoryOver.Groupoids

end CategoryTheory
