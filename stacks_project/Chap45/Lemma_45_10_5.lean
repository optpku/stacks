/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Trace.AlgHom
import StacksCheckRecall

@[expose] public section

universe u v w x

/- Lemma 45.10.5: corrected conclusion of Stacks tag 0FHT. Under the stated integral
trace relation, the two surjective maps have equal kernels. The source's literal equality
of maps is false: the identity and factor swap on `ℚ × ℚ` have identical traces. Its
primitive-idempotent argument proves equality of kernels, which is the correction checked
here; the authoritative source text is unchanged. -/
@[stacks 0FHT] #check
  (@AlgHom.ker_eq_of_trace_relation :
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
      RingHom.ker σ = RingHom.ker σ')
