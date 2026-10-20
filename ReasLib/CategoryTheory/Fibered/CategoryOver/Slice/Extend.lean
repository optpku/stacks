/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.StrictSlice
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Strict
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Composition
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Extension along a fibration in groupoids

Postcomposition with a fibration in groupoids `G : B ⥤ C` sends a fibred
category over `B` to a fibred category over `C`, equipped with its canonical
morphism to `FiberedCategoryOver.ofFunctor G`.  This construction is
independent of any topology or stack condition. A faithful such `G` also gives
the functorial action in `Slice.Extend.Functor`; taking `G = Over.forget U`
recovers extension from the slice base `C/U`.
-/

@[expose] public section

universe uB vB uC vC

namespace CategoryTheory.FiberedCategoryOver.Slice.Extend

open Bicategory
open scoped CategoryTheory.Bicategory

variable {B : Type uB} {C : Type uC}
variable [Category.{vB} B] [Category.{vC} C]

namespace basedHom

/-- The projection of `X` commutes with the projections of its extension along
`G` and the canonical fibred category of `G`. -/
theorem comm (G : B ⥤ C) [G.IsFibered]
    (X : FiberedCategoryOver.{uB, vB, uB, vB} B) :
    X.p ⋙ (FiberedCategoryOver.ofFunctor G).p = (X.comp G).p := sorry

end basedHom

/-- The based functor underlying the structural morphism of `X.comp G`. -/
def basedHom (G : B ⥤ C) [G.IsFibered]
    (X : FiberedCategoryOver.{uB, vB, uB, vB} B) :
    (X.comp G).toBasedCategory ⥤ᵇ
      (FiberedCategoryOver.ofFunctor G).toBasedCategory :=
  BasedFunctor.ofFunctor X.p (basedHom.comm G X)

namespace basedHom

/-- The structural based functor preserves strongly cartesian morphisms because
`G` is fibred in groupoids. -/
theorem preservesStronglyCartesian (G : B ⥤ C)
    [Functor.IsFibered.InGroupoids G]
    (X : FiberedCategoryOver.{uB, vB, uB, vB} B) :
    (basedHom G X).PreservesStronglyCartesian := sorry

end basedHom

/-- The extension of `X` carries its canonical morphism to the fibred category
associated to `G`. -/
def hom (G : B ⥤ C) [Functor.IsFibered.InGroupoids G]
    (X : FiberedCategoryOver.{uB, vB, uB, vB} B) :
    X.comp G ⟶ FiberedCategoryOver.ofFunctor G :=
  FiberedCategoryOver.ofBasedFunctor
    (basedHom G X) (basedHom.preservesStronglyCartesian G X)

namespace hom

/-- The total functor of the structural morphism is the original projection to
`B`. -/
@[simp]
theorem toFunctor (G : B ⥤ C) [Functor.IsFibered.InGroupoids G]
    (X : FiberedCategoryOver.{uB, vB, uB, vB} B) :
    FiberedCategoryOver.toFunctor (hom G X) = X.p := sorry

end hom

/-- Package the extended fibred category and its structural morphism as an
object of the strict slice over the fibred category associated to `G`. -/
def obj (G : B ⥤ C) [Functor.IsFibered.InGroupoids G]
    (X : FiberedCategoryOver.{uB, vB, uB, vB} B) :
    StrictSlice (FiberedCategoryOver.ofFunctor G) :=
  StrictSlice.mk (X.comp G) (hom G X)

end CategoryTheory.FiberedCategoryOver.Slice.Extend
