module

public import ReasLib.Algebra.Module.End.FiniteLength

@[expose] public section

noncomputable section

open scoped BigOperators

universe u v w

namespace Module.End

/-- The finite-length determinant is the product of the component determinants after an
intertwining linear equivalence with a finite product. -/
theorem finiteLengthDeterminant_eq_prod_of_equiv_pi
    {R : Type u} [CommRing R] [IsLocalRing R]
    {ι : Type v} [Fintype ι] {M : Type w} {N : ι → Type w}
    [AddCommGroup M] [Module R M] [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (hM : IsFiniteLength R M) (hN : ∀ i, IsFiniteLength R (N i))
    (φ : Module.End R M) (ψ : ∀ i, Module.End R (N i))
    (e : M ≃ₗ[R] ∀ i, N i) (he : ∀ x i, e (φ x) i = ψ i (e x i)) :
    φ.finiteLengthDeterminant hM =
      ∏ i, (ψ i).finiteLengthDeterminant (hN i) := sorry

end Module.End

end
