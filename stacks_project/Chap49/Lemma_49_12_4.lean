/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.NoetherPairing.LocalizedPresentation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 49.12.4: for a quasi-finite algebra presented by `n` equations in the
localization of `A[x₁, …, xₙ]` away from `h`, the relative dualizing module is
`B`-linearly equivalent to `B`, with the Jacobian determinant mapping to the trace element. -/
@[stacks 0BWH] #check
  (Algebra.LocalizedPresentation.exists_relativeDualizingEquiv :
    ∀ (A B' B : Type u) [CommRing A] [CommRing B'] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [Algebra A B'] [Algebra B' B] [Algebra A B]
      [IsScalarTower A B' B] [Algebra.FiniteType A B]
      [Algebra.QuasiFinite A B] [Module.Finite A B']
      {n : ℕ} (hn : 1 ≤ n) (h : MvPolynomial (Fin n) A)
      (f : Fin n → MvPolynomial (Fin n) A)
      (q : Localization.Away h →ₐ[A] B)
      (h_q : Function.Surjective q)
      (h_ker_q : RingHom.ker q.toRingHom =
        Ideal.span (Set.range fun i ↦
          algebraMap (MvPolynomial (Fin n) A) (Localization.Away h) (f i)))
      (h_open : IsOpenImmersion
        (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
      (τ : Algebra.RelativeDualizingModule.of A B' B
        (Algebra.FiniteType.QuasiFinite.of_quasiFinite inferInstance) h_open)
      (hτ : @Algebra.RelativeDualizingModule.TraceElement.IsUniversal A B' B _ _ _ _ _ _ _ _ _
        (RingHom.flat_algebraMap_iff.mp
          (Algebra.LocalizedPresentation.syntomic hn h f q h_q h_ker_q).flat)
        (Algebra.FiniteType.QuasiFinite.of_quasiFinite inferInstance) _ h_open τ),
        ∃ e : B ≃ₗ[B] Algebra.RelativeDualizingModule.of A B' B
          (Algebra.FiniteType.QuasiFinite.of_quasiFinite inferInstance) h_open,
        e (q (algebraMap (MvPolynomial (Fin n) A) (Localization.Away h)
          (Matrix.det (fun i j ↦ MvPolynomial.pderiv j (f i))))) = τ)
