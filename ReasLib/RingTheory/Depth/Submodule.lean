/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Length
public import ReasLib.RingTheory.Depth

@[expose] public section

universe u v

open IsLocalRing
open scoped ENat

namespace Submodule

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (N : Submodule R M)

/-- The inverse image in `M` of the maximal-ideal primary component of `M ⧸ N`. -/
abbrev comapMkQPrimaryComponent : Submodule R M :=
  comap N.mkQ ((maximalIdeal R).primaryComponent (M ⧸ N))

/-- The submodule `N` is contained in the inverse image of the maximal-ideal primary
component of `M ⧸ N`. -/
theorem le_comapMkQPrimaryComponent : N ≤ comapMkQPrimaryComponent N := sorry

variable [IsNoetherianRing R] [Module.Finite R M]

/-- A nonzero submodule of a finite module of depth at least two has depth at least one. -/
theorem moduleDepth_ge_one (hM : (2 : ℕ∞) ≤ moduleDepth R M) (hN : N ≠ ⊥) :
    (1 : ℕ∞) ≤ moduleDepth R N := sorry

/-- For a nonzero submodule of a finite module of depth at least two, depth one is
equivalent to depth zero of the quotient. -/
theorem moduleDepth_eq_one_iff (hM : (2 : ℕ∞) ≤ moduleDepth R M) (hN : N ≠ ⊥) :
    moduleDepth R N = 1 ↔ moduleDepth R (M ⧸ N) = 0 := sorry

/-- The quotient of the inverse-image enlargement by the original submodule has finite
length. -/
theorem length_comapMkQPrimaryComponent_quotient_lt_top :
    Module.length R
        (comapMkQPrimaryComponent N ⧸ N.submoduleOf (comapMkQPrimaryComponent N)) < ⊤ := sorry

/-- The inverse-image enlargement of a submodule in a module of depth at least two has
depth at least two. -/
theorem moduleDepth_comapMkQPrimaryComponent_ge_two
    (hM : (2 : ℕ∞) ≤ moduleDepth R M) (hN : N ≠ ⊥) :
    (2 : ℕ∞) ≤ moduleDepth R (comapMkQPrimaryComponent N) := sorry

end Submodule
