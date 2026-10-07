module

public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite free complexes concentrated in degree zero

This leaf records the canonical consequence of a vanishing positive-degree
rank profile.  It is intentionally a proposition-level existence statement:
downstream arguments may eliminate the exhibited isomorphism without exposing
a noncanonical global choice of coordinates.
-/

@[expose] public section

universe u

open CategoryTheory ChainComplex

namespace FiniteFreeComplex

variable {R : Type u} [Ring R]
variable {e : ℕ}

namespace positiveRankSum

/-- If the positive-degree rank sum of a bounded finite free complex vanishes, its underlying
chain complex is isomorphic to the degree-zero single complex on its displayed degree-zero term. -/
@[stacks 00MS "finite-free complex concentrated in degree zero"]
theorem nonempty_iso_single₀_of_eq_zero
    (C : _root_.FiniteFreeComplex R e) (hzero : positiveRankSum C = 0) :
    Nonempty
      (C.toChainComplex ≅
        ((ChainComplex.single₀ (ModuleCat R)).obj
          (ModuleCat.of R (Fin (C.rank ⟨0, Nat.zero_lt_succ e⟩) → R)))) := sorry

end positiveRankSum

end FiniteFreeComplex
