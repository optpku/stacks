/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Homotopy
import StacksCheckRecall

@[expose] public section

open CategoryTheory HomologicalComplex ComplexShape

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V]
variable (K L : ChainComplex V ℤ) (f : K ⟶ L)

/- Definition 12.13.2 [010X]: homotopy equivalence is represented by the canonical bundled
forward map, inverse map, and two homotopies. -/
@[stacks 010X]
#check (HomotopyEquiv K L : Type _)

#check (HomologicalComplex.homotopyEquivalences V (down ℤ) f : Prop)
