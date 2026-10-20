/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSmoothLocal

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Étale morphisms of algebraic spaces are étale-smooth local on the
source-and-target. -/
instance Etale.isEtaleSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsEtaleSmoothLocalAtSourceAndTarget (@Etale S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
