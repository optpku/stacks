/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Presheaf.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids

universe u w

variable {S : Scheme.{u}} (X : GroupoidsOver S)

/- Definition 96.3.1: let `p : X ⟶ (Sch/S)_fppf` be a category fibred in
groupoids. A presheaf on `X` is a `Type`-valued presheaf on the underlying
category of `X`. A morphism of presheaves on `X` is a morphism of those
presheaves. We denote `PSh(X)` the functor category `Presheaf X.total`. -/
@[stacks 06TJ] #check
  (CategoryTheory.Presheaf.{u + 1, u, w} X.total : Type (max (u + 1) (w + 1)))

variable {F G : CategoryTheory.Presheaf.{u + 1, u, w} X.total}

/- Morphisms of presheaves on `X` are morphisms in `Presheaf X.total`. -/
#check (CategoryTheory.PresheafWithValues.Hom F G : Type (max (u + 1) w))
