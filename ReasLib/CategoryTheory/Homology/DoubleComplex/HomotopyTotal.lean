/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.HomotopyTotal.Triangulated

/-!
# Totalization of double complexes on homotopy categories

This file is the public facade for homotopy-category totalization. The implementation is split
into basic descent, shift compatibility, and exactness layers so that direct imports can remain
small.
-/
