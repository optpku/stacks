module

import StacksCheckRecall
public import ReasLib.RingTheory.Etale.Weakly.MaximalSubalgebra

/-!
@stack 0CKS
-/

@[expose] public section

universe u v

open scoped WeaklyEtale

/- Lemma 15.106.2, tag `0CKS`: over a field, the supremum of the weakly etale subalgebras of a
commutative algebra is itself weakly etale and contains every weakly etale subalgebra. -/
@[stacks 0CKS "Lemma 15.106.2"]
#check fun (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A] ↦
  (Subalgebra.maximalWeaklyEtale.isGreatest (K := K) (A := A) :
    IsGreatest {B : Subalgebra K A | Algebra.WeaklyEtale K B} B_max(A⁄K))

#check @Subalgebra.maximalWeaklyEtale
#check @Subalgebra.maximalWeaklyEtale.weaklyEtale
#check @Subalgebra.maximalWeaklyEtale.le
#check @Subalgebra.maximalWeaklyEtale.mem_iff
