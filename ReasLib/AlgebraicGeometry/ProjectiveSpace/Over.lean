/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Standard projective space over an affine base

This leaf packages the canonical standard projective-space morphism as an object of the slice over
`Spec(R)`.  The underlying scheme and structure-map readouts are kept next to the bundled object so
slice-category consumers do not need to unfold the `Over` construction.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The standard projective `n`-space over the affine base `Spec(R)`, bundled as a slice object. -/
@[stacks 01JE "standard projective space over its affine base"]
abbrev schemeOver (R : Type u) [CommRing R] (n : ℕ) :
    Over (Spec (CommRingCat.of R)) :=
  Over.mk (toSpec R n)

/-- The underlying scheme of `ProjectiveSpace.schemeOver R n` is standard projective space. -/
@[simp, stacks 01JE "underlying standard projective space"]
theorem schemeOver_left (R : Type u) [CommRing R] (n : ℕ) :
    (schemeOver R n).left = scheme R n := sorry

/-- The structure morphism of `ProjectiveSpace.schemeOver R n` is `toSpec R n`. -/
@[simp, stacks 01JE "standard projective-space structure map in the slice"]
theorem schemeOver_hom (R : Type u) [CommRing R] (n : ℕ) :
    (schemeOver R n).hom = toSpec R n := sorry

end AlgebraicGeometry.ProjectiveSpace
