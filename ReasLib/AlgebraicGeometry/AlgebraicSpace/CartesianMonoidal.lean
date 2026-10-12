/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-! Cartesian monoidal structures on slices of algebraic spaces. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The slice of algebraic spaces over `B` has its canonical Cartesian monoidal structure. -/
noncomputable instance instCartesianMonoidalCategoryOver
    {S : Scheme.{u}} (B : AlgebraicSpace S) :
    CartesianMonoidalCategory (Over B) :=
  Over.cartesianMonoidalCategory B

/-- The canonical Cartesian monoidal structure on algebraic spaces over `B` is braided. -/
noncomputable instance instBraidedCategoryOver
    {S : Scheme.{u}} (B : AlgebraicSpace S) : BraidedCategory (Over B) :=
  Over.braidedCategory B

/-- The slice over an algebraic space over `B` has its canonical Cartesian monoidal structure. -/
noncomputable instance instCartesianMonoidalCategoryOverOver
    {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :
    CartesianMonoidalCategory (Over U) :=
  Over.cartesianMonoidalCategory U

/-- The canonical Cartesian monoidal structure on the slice over `U` is braided. -/
noncomputable instance instBraidedCategoryOverOver
    {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) : BraidedCategory (Over U) :=
  Over.braidedCategory U

end AlgebraicGeometry.AlgebraicSpace
