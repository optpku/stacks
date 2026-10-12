/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.StrictCostructuredArrow.Basic
public import ReasLib.CategoryTheory.Bicategory.StrictCostructuredArrow.Computations
public import ReasLib.CategoryTheory.Bicategory.StrictCostructuredArrow.Projection

/-!
# Strict costructured arrows

Stable aggregate for the generic strict costructured-arrow construction. Use
`Basic`, `Projection`, or `Computations` directly when only one layer is needed.
-/

@[expose] public section
