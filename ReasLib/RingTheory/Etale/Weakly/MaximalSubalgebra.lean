module

public import ReasLib.RingTheory.Etale.Weakly.Field
import Mathlib.Tactic.CrossRefAttribute

/-!
# Maximal weakly etale subalgebras over fields

For a field `K` and a commutative `K`-algebra `A`, this file owns the greatest weakly etale
`K`-subalgebra of `A`.  The concrete owner is the supremum in `Subalgebra K A`; its universal
property, canonical weakly etale instance, and elementwise API are exposed separately.

The field hypothesis is intentional.  Over a general base ring, images of weakly etale algebras
need not provide the closure property used to prove that this supremum is itself weakly etale.
@stack 0CKS
-/

@[expose] public section

universe u v

namespace Subalgebra

variable (K : Type u) [Field K]
variable (A : Type v) [CommRing A] [Algebra K A]

/-- The supremum of the weakly etale `K`-subalgebras of `A`. -/
@[stacks 0CKS "maximal weakly etale subalgebra"]
def maximalWeaklyEtale : Subalgebra K A :=
  sSup {B : Subalgebra K A | Algebra.WeaklyEtale K B}

namespace maximalWeaklyEtale

/-- `maximalWeaklyEtale K A` is the greatest weakly etale `K`-subalgebra of `A`. -/
@[stacks 0CKS "greatest weakly etale subalgebra"]
theorem isGreatest :
    IsGreatest {B : Subalgebra K A | Algebra.WeaklyEtale K B}
      (Subalgebra.maximalWeaklyEtale K A) := sorry

/-- The maximal weakly etale subalgebra carries its canonical weakly etale instance. -/
@[stacks 0CKS "maximal weakly etale subalgebra instance"]
instance weaklyEtale :
    Algebra.WeaklyEtale K (Subalgebra.maximalWeaklyEtale K A) := sorry

/-- Every weakly etale `K`-subalgebra of `A` lies in `maximalWeaklyEtale K A`. -/
@[stacks 0CKS "weakly etale subalgebras lie in the maximal one"]
theorem le (B : Subalgebra K A) (hB : Algebra.WeaklyEtale K B) :
    B ≤ Subalgebra.maximalWeaklyEtale K A := sorry

/-- An element lies in the maximal weakly etale subalgebra exactly when it lies in some weakly
etale subalgebra. -/
@[stacks 0CKS "membership in the maximal weakly etale subalgebra"]
theorem mem_iff {x : A} :
    x ∈ Subalgebra.maximalWeaklyEtale K A ↔
      ∃ B : Subalgebra K A, Algebra.WeaklyEtale K B ∧ x ∈ B := sorry

end maximalWeaklyEtale

end Subalgebra

namespace WeaklyEtale

@[inherit_doc Subalgebra.maximalWeaklyEtale]
scoped notation:max "B_max(" A "⁄" K ")" => Subalgebra.maximalWeaklyEtale K A

end WeaklyEtale

open scoped WeaklyEtale
