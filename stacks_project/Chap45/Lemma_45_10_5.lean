module

public import ReasLib.RingTheory.Trace.AlgHom
import StacksCheckRecall

@[expose] public section

universe u v w x

/- Lemma 45.10.5: over a field `F` of characteristic zero, two surjective maps from a
finite `F`-algebra to the same finite separable `F`-algebra are equal if the difference of
their trace composites is an integer multiple `n > 1` of an integral linear combination of
trace composites through finite separable `F`-algebras. -/
@[stacks 0FHT] #check
  (@AlgHom.eq_of_trace_relation :
    ∀ {F : Type u} [Field F] [CharZero F]
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
          n • ∑ i, m i • (Algebra.trace F (Fᵢ i)).comp (σᵢ i).toLinearMap),
      σ = σ')
