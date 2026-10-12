/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.DualNumber.Injective
public import ReasLib.Algebra.Homology.ChainComplex.DualNumber.Periodic

@[expose] public section

/-!
# Termwise injectivity of the dual-number periodic complex

@stack 0A5U
-/

universe u

open CategoryTheory

namespace DualNumber.Periodic

variable (k : Type u) [Field k]

/-- Every term of the periodic dual-number complex over a field is injective. -/
@[stacks 0A5U "termwise injectivity of the periodic resolution"]
instance termInjective (n : ℕ) : Injective ((complex k).X n) := sorry

#synth Injective ((complex k).X 0)

end DualNumber.Periodic
