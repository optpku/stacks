/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.Centralizer.Simplicity
public import ReasLib.Algebra.CentralSimple.Centralizer.DoubleCentralizer
public import ReasLib.Algebra.CentralSimple.Centralizer.TensorProduct
public import ReasLib.Algebra.CentralSimple.Centralizer.MaximalCommutative

/-! # Centralizer Theory in Central Simple Algebras

Sub-modules for the centralizer and double centralizer theorems.

- `Simplicity` — centralizer of a simple subalgebra is simple
- `Dimension` — dimension formula [A:k] = [B:k]·[C_A(B):k]
- `DoubleCentralizer` — C_A(C_A(B)) = B
- `TensorProduct` — B ⊗ C_A(B) ≃ₐ A
- `MaximalCommutative` — maximal commutative subalgebras and subfields
-/
