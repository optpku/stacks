/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiDM.Cover

/-!
# Locally quasi-finite flat algebraic-space covers

The algebraic-space covering predicate is available from its shared owner.
-/

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicStack.existsLocallyQuasiFiniteFlatSpaceCover :
  {S : Scheme.{u}} → (X : GroupoidsOver S) → [AlgebraicStack X] → Prop)
