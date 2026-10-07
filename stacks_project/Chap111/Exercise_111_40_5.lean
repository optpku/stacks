module

public import ReasLib.RingTheory.Polynomial.Picard
import StacksCheckRecall

@[expose] public section

universe u
/- Exercise 111.40.5 (1): for a field `k`, every invertible module over `k[X]` is
free of rank 1, equivalently linearly equivalent to `k[X]`. -/
@[stacks 02AH] #check (@Polynomial.invertibleModule_linearEquiv :
  ∀ (k : Type u), [Field k] → (M : Type u) → [AddCommGroup M] →
    [Module (Polynomial k) M] → [Module.Invertible (Polynomial k) M] →
      Nonempty (M ≃ₗ[Polynomial k] Polynomial k))

/- Exercise 111.40.5 (2): if `k` is a field with nontrivial unit group, then the
equal-endpoint algebra `{f ∈ k[X] | f.eval 0 = f.eval 1}` admits a nontrivial
invertible module. -/
@[stacks 02AH] #check (@Polynomial.EqualEndpoint.exists_nontrivial_invertibleModule :
  ∀ (k : Type u), [Field k] → [Nontrivial kˣ] →
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module (Polynomial.equalEndpoint k) M)
      (_ : Module.Invertible (Polynomial.equalEndpoint k) M),
      ¬ Module.Free (Polynomial.equalEndpoint k) M)

/- Exercise 111.40.5 (3): for any field `k`, including the field with two elements,
the cusp subalgebra `k[X ^ 2, X ^ 3] ⊆ k[X]` admits a nontrivial invertible module. -/
@[stacks 02AH] #check (@Polynomial.Cusp.exists_nontrivial_invertibleModule :
  ∀ (k : Type u), [Field k] →
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module (Polynomial.cuspSubalgebra k) M)
      (_ : Module.Invertible (Polynomial.cuspSubalgebra k) M),
      ¬ Module.Free (Polynomial.cuspSubalgebra k) M)
