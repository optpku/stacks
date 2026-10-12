/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Coherent.MvPolynomial
public import ReasLib.RingTheory.MvPolynomial.Noetherian
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import StacksCheckRecall

@[expose] public section

/- Example 17.12.3 (01BX) (1): the polynomial ring `MvPolynomial ℕ+ ℂ` in countably many
variables is coherent. -/
@[stacks 01BX "(1)"]
#check (inferInstance : IsCoherentRing (MvPolynomial ℕ+ ℂ))

/- Example 17.12.3 (01BX) (2): the polynomial ring `MvPolynomial ℕ+ ℂ` is not
Noetherian. -/
@[stacks 01BX "(2)"]
#check (MvPolynomial.not_isNoetherianRing_of_infinite (σ := ℕ+) (R := ℂ))
