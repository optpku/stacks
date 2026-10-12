/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Multiplication maps of group objects
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.MonObj

universe v u

namespace CategoryTheory.GrpObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- The multiplication-by-`n` endomorphism of a group object. -/
noncomputable abbrev mulBy (G : C) [GrpObj G] (n : ℕ) : G ⟶ G :=
  (𝟙 G) ^ n

end CategoryTheory.GrpObj
