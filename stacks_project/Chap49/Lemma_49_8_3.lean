/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DedekindDifferent.Comparison
import StacksCheckRecall

@[expose] public section

open scoped Algebra.DualModule Algebra.TensorProduct.Right TensorProduct TensorProduct.Right

universe u

/- Lemma 49.8.3: if the Dedekind different of `A → B` is defined and `A → B`
is flat, then the canonical comparison sends `1` to the trace element, and
the Dedekind different is characterized by the trace-element span. -/
@[stacks 0BW3] #check
  (Algebra.RelativeDualizingModule.dedekindComparison_one_eq_traceElement :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
      [IsNoetherianRing A] [IsNoetherianRing B] [Module.Finite A B]
      [Module.Flat A B]
      (h_regular : ∀ a ∈ nonZeroDivisors A,
        algebraMap A B a ∈ nonZeroDivisors B)
      [Algebra.Etale (FractionRing A) (B ⊗[A] FractionRing A)],
      let one : Submodule.dedekindComplementary A (FractionRing A) B
          (B ⊗[A] FractionRing A) :=
        ⟨1, (_root_.dedekindTrace_mem_base_iff_one_mem_complementary
          (A := A) (B := B) h_regular).mp
          (_root_.dedekindTrace_mem_base_of_flat (A := A) (B := B) h_regular)⟩
      (Algebra.RelativeDualizingModule.dedekindComparison A B one) ⊗ₜ[B] (1 : B) =
        Algebra.RelativeDualizingModule.finiteFlatTraceElement A B)

@[stacks 0BW3] #check
  (Algebra.RelativeDualizingModule.mem_dedekindDifferent_iff_smul_mem_span :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
      [IsNoetherianRing A] [IsNoetherianRing B] [Module.Finite A B]
      [Module.Flat A B]
      (h_regular : ∀ a ∈ nonZeroDivisors A,
        algebraMap A B a ∈ nonZeroDivisors B)
      [Algebra.Etale (FractionRing A) (B ⊗[A] FractionRing A)]
      (b : B),
      algebraMap B (B ⊗[A] FractionRing A) b ∈
          Submodule.dedekindDifferent A (FractionRing A) B
            (B ⊗[A] FractionRing A) ↔
        ∀ ω : Algebra.RelativeDualizingModule.of A B B (.of_moduleFinite) inferInstance,
          b • ω ∈ Submodule.span B {Algebra.RelativeDualizingModule.finiteFlatTraceElement A B})
