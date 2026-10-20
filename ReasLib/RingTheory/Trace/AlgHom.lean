module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

universe u v w x

namespace AlgHom

/-- Over a characteristic-zero field, two surjective algebra homomorphisms into the same
finite-dimensional separable algebra have the same kernel if the difference of their trace
composites is a proper integral multiple of an integral linear combination of trace composites. -/
theorem ker_eq_of_trace_relation
    {F : Type u} [Field F] [CharZero F]
    {A : Type v} [CommRing A] [Algebra F A] [FiniteDimensional F A]
    {F' : Type w} [CommRing F'] [Algebra F F'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F'] {r : ℕ} (Fᵢ : Fin r → Type x)
    [∀ i, CommRing (Fᵢ i)] [∀ i, Algebra F (Fᵢ i)]
    [∀ i, FiniteDimensional F (Fᵢ i)] [∀ i, Algebra.IsSeparable F (Fᵢ i)]
    (σ σ' : A →ₐ[F] F') (σᵢ : ∀ i, A →ₐ[F] Fᵢ i)
    (hσ : Function.Surjective σ) (hσ' : Function.Surjective σ')
    (n : ℤ) (hn : 1 < n) (m : Fin r → ℤ)
    (htrace :
      (Algebra.trace F F').comp σ.toLinearMap -
          (Algebra.trace F F').comp σ'.toLinearMap =
        n • ∑ i, m i • (Algebra.trace F (Fᵢ i)).comp (σᵢ i).toLinearMap) :
    RingHom.ker σ = RingHom.ker σ' := sorry

end AlgHom
