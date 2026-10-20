/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Canonical
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Spaces

/-! # Subcanonicality of the spaces-étale topology -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The étale topology of algebraic spaces over `X` is subcanonical. -/
instance spacesEtaleTopology.instSubcanonical {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (spacesEtaleTopology X).Subcanonical :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
