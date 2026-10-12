/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Zero morphisms in the category of groups

The trivial group is a zero object, hence it canonically supplies zero morphisms in `GrpCat`.
Exporting this instance avoids rebuilding the same zero-object bridge in kernel arguments.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace GrpCat

/-- The zero object of `GrpCat` canonically determines its zero morphisms. -/
@[stacks 08P0 "zero morphisms in the category of groups"]
noncomputable instance hasZeroMorphisms : HasZeroMorphisms GrpCat.{u} :=
  HasZeroObject.zeroMorphismsOfZeroObject

end GrpCat
