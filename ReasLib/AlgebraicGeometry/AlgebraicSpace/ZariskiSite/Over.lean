/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.OverClass
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiSite

/-!
# Structure morphisms of open subspaces

An open subspace of an algebraic space over a base inherits the structure morphism
obtained by composing its open immersion with the ambient structure morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The structure morphism of an open subspace of `X` over `B` is the composite of the
open immersion with `X ↘ B`. -/
instance instOverClass_smallZariskiSite_left {B : AlgebraicSpace S} [OverClass X B]
    (U : smallZariskiSite X) : OverClass U.left B where
  hom := U.hom ≫ X ↘ B

end AlgebraicGeometry.AlgebraicSpace
