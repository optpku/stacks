module

public import ReasLib.FieldTheory.IsAlgClosed.TwoSubalgebras
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 53.15.1: if a commutative algebra `A` over an algebraically closed field `k`
has exactly two `k`-subalgebras, then `A` is `k`-algebra equivalent to either `k × k`
or the dual numbers `DualNumber k`. Thus the source equalities are understood up to
`k`-algebra equivalence. -/
@[stacks 0C1I] #check (Algebra.nonempty_algEquiv_prod_or_dualNumber_of_two_subalgebras :
  ∀
    {k : Type u} {A : Type v} [Field k] [IsAlgClosed k] [CommRing A] [Nontrivial A]
    [Algebra k A], Nat.card (Subalgebra k A) = 2 →
    Nonempty (A ≃ₐ[k] (k × k)) ∨ Nonempty (A ≃ₐ[k] DualNumber k))
