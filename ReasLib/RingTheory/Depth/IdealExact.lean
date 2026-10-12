/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import ReasLib.RingTheory.Depth.IdealExt

@[expose] public section

open CategoryTheory
open scoped ENat

universe u v

namespace CategoryTheory.ShortComplex.ShortExact

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {S : ShortComplex (ModuleCat.{v} A)}
variable [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃]

/-- For a short exact sequence of finite modules, the ideal-depth of the middle
term is bounded below by the minimum of the ideal-depths of the endpoints. -/
theorem idealDepth_middle_ge_min (I : Ideal A) (hS : S.ShortExact) :
    I.depth S.X₂ ≥ min (I.depth S.X₁) (I.depth S.X₃) := sorry

/-- For a short exact sequence of finite modules, the ideal-depth of the quotient
term is bounded below by the minimum of the middle depth and the predecessor
of the submodule depth. -/
theorem idealDepth_right_ge_min (I : Ideal A) (hS : S.ShortExact) :
    I.depth S.X₃ ≥ min (I.depth S.X₂) (I.depth S.X₁ - 1) := sorry

/-- For a short exact sequence of finite modules, the ideal-depth of the submodule
term is bounded below by the minimum of the middle depth and the successor of
the quotient depth. -/
theorem idealDepth_left_ge_min (I : Ideal A) (hS : S.ShortExact) :
    I.depth S.X₁ ≥ min (I.depth S.X₂) (I.depth S.X₃ + 1) := sorry

end CategoryTheory.ShortComplex.ShortExact
