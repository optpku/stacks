/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Effective
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

section

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [IsLocallyNoetherian S] [LocallyOfFiniteType f]
variable (r : ℕ)

/- Definition 62.8.1: Let `f : X ⟶ S` be a morphism of schemes. Assume `S` is
locally Noetherian and `f` is locally of finite type. Let `r ≥ 0` be an integer.
We say a relative `r`-cycle `α` on `X / S` is effective if `α_s` is an effective
cycle (Chow Homology, Definition 42.8.4) for all `s ∈ S`. The monoid of all
effective relative `r`-cycles on `X / S` is denoted `z^{eff}(X/S, r)`. -/
@[stacks 0H5R] #check
  (AlgebraicGeometry.RelativeCycle.effective f r :
    AddSubmonoid (f.FiberCycleFamily r))

end
