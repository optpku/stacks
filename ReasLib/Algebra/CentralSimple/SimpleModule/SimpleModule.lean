/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.CentralSimple.SimpleModule.Existence
public import ReasLib.Algebra.CentralSimple.SimpleModule.Uniqueness
public import ReasLib.Algebra.CentralSimple.SimpleModule.DirectSum
public import ReasLib.Algebra.CentralSimple.SimpleModule.Endomorphism
public import ReasLib.Algebra.CentralSimple.SimpleModule.DoubleCentralizer

/-! # Simple Module Theory

Sub-modules for the structure theory of simple modules over simple rings.

- `Existence` — finite-dimensional algebras have simple submodules
- `Uniqueness` — simple modules are unique up to linear equivalence
- `DirectSum` — finite modules decompose as direct sums of simples
- `Endomorphism` — End(M) is a division ring; dimension formulas
- `DoubleCentralizer` — bicommutant theorem: A ≃ₐ End(End_A M) M
-/

