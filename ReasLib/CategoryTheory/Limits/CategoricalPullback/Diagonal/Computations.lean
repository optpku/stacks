/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.Computations.Diagonal
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.Computations.Postcompose
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.Computations.ToDiagonal
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.Computations.Comparison

/-!
# Computations for categorical-pullback diagonal constructions

This aggregate keeps the historical `Diagonal.Computations` import stable while the readout API is
split by mathematical owner: relative diagonal, common-base postcomposition, diagonalization, and
the final comparison.
-/
