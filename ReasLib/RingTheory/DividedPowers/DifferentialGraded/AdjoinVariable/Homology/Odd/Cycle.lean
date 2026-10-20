/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.CycleMultiplication
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.AdjoinVariable
import Mathlib.Tactic.CrossRefAttribute

/-!
# The attaching cycle of a degree-one odd cell

This file owns the bundled degree-zero attaching cycle and its multiplication chain map. The
cofiber and homology calculations consume these canonical data rather than rebuilding a raw
closed element locally.
-/

@[expose] public section

noncomputable section

universe u v

namespace DividedPowerChainAlgebra

variable {R : Type u} [CommRing R]

namespace Adjoin

/-- A degree-zero element satisfying the degree-one adjoining-cycle condition, bundled as a
cycle in the underlying chain DGA. -/
@[stacks 0GZ6 "degree-zero attaching cycle"]
def degreeZeroCycle (A : DividedPowerChainAlgebra.{u, v} R)
    (f : A.toChainDGAlgebra.nonnegativePiece 0) (hf : IsCycle A (1 : ℕ+) f) :
    A.toChainDGAlgebra.cycles 0 :=
  IsCycle.toCycle hf

namespace Odd.Extension

variable {A : DividedPowerChainAlgebra.{u, v} R}
variable {f : A.toChainDGAlgebra.nonnegativePiece 0}

/-- The attaching element of a degree-one odd cell, bundled as a cycle using the closedness
intrinsic to the cell presentation. -/
@[stacks 0GZ6 "degree-one odd-cell attaching cycle"]
def attachingCycle (X : Odd.Extension A (1 : ℕ+) f) : A.toChainDGAlgebra.cycles 0 :=
  Cell.attachingCycle X.toCell

/-- The canonical attaching chain endomorphism of a degree-one odd cell, given by right
multiplication by its bundled attaching cycle. -/
@[stacks 0GZ6 "degree-one odd-cell attaching chain map"]
def attachingMap (X : Odd.Extension A (1 : ℕ+) f) :
    A.toChainDGAlgebra.toChainComplex ⟶ A.toChainDGAlgebra.toChainComplex :=
  ChainDGAlgebra.Cycle.rightMulCycle A.toChainDGAlgebra X.attachingCycle

/-- The components of the odd-cell attaching map are right multiplication by the underlying
attaching element. -/
@[simp]
theorem attachingMap_f (X : Odd.Extension A (1 : ℕ+) f) (n : ℤ) :
    X.attachingMap.f n =
      ModuleCat.ofHom (ChainDGAlgebra.Cycle.rightMulApp A.toChainDGAlgebra f n) := sorry

end Odd.Extension

end Adjoin

end DividedPowerChainAlgebra
