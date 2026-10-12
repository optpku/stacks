/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChernClass.Theory

@[expose] public section

open AlgebraicGeometry.ChernClass

/-! Compatibility surface for the reusable Chern-class theory API. -/
#check AlgebraicGeometry.ChernClass.clopenComplement
#check AlgebraicGeometry.ChernClass.tautologicalPicardClass
#check AlgebraicGeometry.ChernClass.Theory
#check AlgebraicGeometry.ChernClass.Theory.ofAxioms
