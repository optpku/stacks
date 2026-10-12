/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Step.Upper
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Step.Lower
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

@[expose] public section

/-!
# Truncation Triangles in a Derived Category

This compatibility facade collects the canonical Mathlib truncation triangle,
the bundled single-degree piece, and the two adjacent-step specializations.
The mathematical owners remain in the focused imported modules:

* `t.triangleLEGE` and `t.triangleLEGE_distinguished` own the basic
  `t`-structure truncation triangle;
* `DerivedCategory.Truncation.Piece` owns the degree-`n` full-subcategory lift
  and its canonical homology cospan;
* `DerivedCategory.TruncLE.Step` and `DerivedCategory.TruncGE.Step` own the
  upper and lower adjacent-step views.

In particular, this facade does not select inverses from deferred `IsIso`
proofs or duplicate Mathlib's triangle data.
-/

open CategoryTheory
open DerivedCategory.TStructure

end
