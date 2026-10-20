/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk
import StacksCheckRecall

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

/- Definition 59.29.6: the stalk of a presheaf on the small étale site at a
geometric point is the colimit over pointed étale neighborhoods. -/
@[stacks 040R] #check (AlgebraicGeometry.Scheme.Etale.stalk :
  {S : Scheme.{u}} → Scheme.GeometricPoint S → (S.Etaleᵒᵖ ⥤ Type u) → Type u)
