/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Category.ModuleCat.Semi

@[expose] public section

/-!
# Factorisations of linear maps

This is the cross-universe, semiring-level analogue of `CategoryTheory.Factorisation`.  The
midpoint is a bundled semimodule, so consumers do not reconstruct its algebraic structures.
-/

universe u v w

namespace LinearMap

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- A factorisation of a linear map through a module in the common endpoint universe. -/
structure Factorisation (f : M →ₗ[R] N) where
  /-- The intermediate module. -/
  mid : SemimoduleCat.{max u v w} R
  /-- The map from the source to the midpoint. -/
  fromSource : M →ₗ[R] mid
  /-- The map from the midpoint to the target. -/
  toTarget : mid →ₗ[R] N
  /-- The two maps compose to the original map. -/
  factor : toTarget.comp fromSource = f

namespace Factorisation

variable {f : M →ₗ[R] N}

/-- Build a linear-map factorisation from its midpoint and two maps. -/
def ofMaps (P : Type (max u v w)) [AddCommMonoid P] [Module R P]
    (fromSource : M →ₗ[R] P) (toTarget : P →ₗ[R] N)
    (factor : toTarget.comp fromSource = f) : Factorisation f where
  mid := SemimoduleCat.of R P
  fromSource := fromSource
  toTarget := toTarget
  factor := factor

end Factorisation

end LinearMap
