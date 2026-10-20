/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Biproduct
public import ReasLib.CategoryTheory.Filtration.Strict.Abelian
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullbacks of Filtered Objects

The pullback of `f : B ⟶ A` and `g : C ⟶ A` is modeled as the filtered kernel of
`biprod.desc f (-g)`.  This reuses the canonical filtered biproduct and induced kernel
filtration, and supplies the standard Mathlib `HasPullback` interface to downstream files.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

noncomputable section

namespace CategoryTheory.FilteredObject.Hom

open FilteredObject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B D : FilteredObject C}

/-- The difference morphism `(f, -g) : B ⊞ D ⟶ A` whose kernel models the pullback. -/
private abbrev pullbackDifference (f : B ⟶ A) (g : D ⟶ A) : (B ⊞ D) ⟶ A :=
  biprod.desc f (-g)

/-- The canonical filtered pullback model as the filtered kernel of `(f, -g)`. -/
private abbrev pullbackModel (f : B ⟶ A) (g : D ⟶ A) : FilteredObject C :=
  kernel (pullbackDifference f g)

/-- The first projection from the filtered-kernel pullback model. -/
private abbrev pullbackModelFst (f : B ⟶ A) (g : D ⟶ A) : pullbackModel f g ⟶ B :=
  kernelι (pullbackDifference f g) ≫ biprod.fst

/-- The second projection from the filtered-kernel pullback model. -/
private abbrev pullbackModelSnd (f : B ⟶ A) (g : D ⟶ A) : pullbackModel f g ⟶ D :=
  kernelι (pullbackDifference f g) ≫ biprod.snd

/-- The filtered-kernel model satisfies the pullback universal property. -/
private theorem pullbackModel_isPullback (f : B ⟶ A) (g : D ⟶ A) :
    IsPullback (pullbackModelFst f g) (pullbackModelSnd f g) f g := sorry

/-- Filtered objects in an abelian category have pullbacks. -/
noncomputable instance hasPullback (f : B ⟶ A) (g : D ⟶ A) : HasPullback f g :=
  (pullbackModel_isPullback f g).hasPullback

/-- In any pullback square of filtered objects, pulling back a strict left leg produces a strict
right leg. -/
@[stacks 05SN]
theorem strict_snd_of_isPullback_of_strict
    (f : B ⟶ A) (g : D ⟶ A) {P : FilteredObject C} {g' : P ⟶ B} {f' : P ⟶ D}
    (sq : IsPullback g' f' f g) (hf : Strict f) : Strict f' := sorry

/-- In the canonical pullback square, the pullback of a strict morphism is strict. -/
@[stacks 05SN]
theorem strict_pullback_snd_of_strict (f : B ⟶ A) (g : D ⟶ A) (hf : Strict f) :
    Strict (pullback.snd f g : pullback f g ⟶ D) := sorry

end CategoryTheory.FilteredObject.Hom
