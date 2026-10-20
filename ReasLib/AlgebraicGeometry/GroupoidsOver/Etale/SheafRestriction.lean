/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Restriction

/-!
# Small-étale sheaf restriction along an object of a groupoid fibration

An étale sheaf on a category fibred in groupoids restricts along an object
`x` to a sheaf on the small étale site of `U = p(x)`, by packaging the
presheaf restriction `restrictSmallEtale`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- Restriction of an étale sheaf on `X` to the small étale site of `U = p(x)`,
obtained by packaging `restrictSmallEtale x F.obj`. -/
def restrictSmallEtaleSheaf (F : Sheaf X.etaleTopology (Type (u + 1))) (x : X.total) :
    Sheaf (X.p.obj x).left.smallEtaleTopology (Type (u + 1)) where
  obj := restrictSmallEtale x F.obj
  property := sorry

/-- The underlying presheaf of `restrictSmallEtaleSheaf F x` is
`restrictSmallEtale x F.obj`. -/
theorem restrictSmallEtaleSheaf_obj (F : Sheaf X.etaleTopology (Type (u + 1)))
    (x : X.total) :
    (restrictSmallEtaleSheaf F x).obj = restrictSmallEtale x F.obj :=
  sorry

end AlgebraicGeometry.GroupoidsOver
