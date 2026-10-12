/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import ReasLib.Algebra.Module.RelativeDualizing
public import ReasLib.Algebra.Module.RelativeDualizing.TraceElement
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.DedekindDifferent.Integrality
public import ReasLib.RingTheory.DedekindDifferent.TraceDual

@[expose] public section

open scoped Algebra.DualModule TensorProduct Algebra.TensorProduct.Right

universe u v

namespace Algebra.RelativeDualizingModule

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

/-- The unique value in `A` whose image in `FractionRing A` is the trace pairing
of `x` with `b`. -/
noncomputable def dedekindTraceValue
    (x : Submodule.dedekindComplementary A (FractionRing A) B
      (B ⊗[A] FractionRing A)) (b : B) : A :=
  Classical.choose (x.property b)

/-- The chosen trace value maps to the trace pairing in `FractionRing A`. -/
theorem dedekindTraceValue_spec
    (x : Submodule.dedekindComplementary A (FractionRing A) B
      (B ⊗[A] FractionRing A)) (b : B) :
    algebraMap A (FractionRing A) (dedekindTraceValue A B x b) =
      Algebra.trace (FractionRing A) (B ⊗[A] FractionRing A)
        (algebraMap B (B ⊗[A] FractionRing A) b * x) := sorry

/-- The trace value is additive in its argument from `B`. -/
theorem dedekindTraceValue_add_right
    (x : Submodule.dedekindComplementary A (FractionRing A) B
      (B ⊗[A] FractionRing A)) (b₁ b₂ : B) :
    dedekindTraceValue A B x (b₁ + b₂) =
      dedekindTraceValue A B x b₁ + dedekindTraceValue A B x b₂ := sorry

/-- The trace value is `A`-linear in its argument from `B`. -/
theorem dedekindTraceValue_smul_right
    (x : Submodule.dedekindComplementary A (FractionRing A) B
      (B ⊗[A] FractionRing A)) (a : A) (b : B) :
    dedekindTraceValue A B x (a • b) = a • dedekindTraceValue A B x b := sorry

/-- The trace pairing with a complementary element, regarded as an `A`-linear functional. -/
noncomputable def dedekindTraceFunctional
    (x : Submodule.dedekindComplementary A (FractionRing A) B
      (B ⊗[A] FractionRing A)) : Module.Dual A B where
  toFun := fun b ↦ dedekindTraceValue A B x b
  map_add' := dedekindTraceValue_add_right A B x
  map_smul' := dedekindTraceValue_smul_right A B x

/-- The trace functional is additive in its complementary-module argument. -/
theorem dedekindTraceFunctional_add
    (x y : Submodule.dedekindComplementary A (FractionRing A) B
      (B ⊗[A] FractionRing A)) :
    dedekindTraceFunctional A B (x + y) =
      dedekindTraceFunctional A B x + dedekindTraceFunctional A B y := sorry

/-- The trace functional respects the `B`-action on the complementary module. -/
theorem dedekindTraceFunctional_smul
    (b : B) (x : Submodule.dedekindComplementary A (FractionRing A) B
      (B ⊗[A] FractionRing A)) :
    dedekindTraceFunctional A B (b • x) = b • dedekindTraceFunctional A B x := sorry

/-- The canonical trace-pairing map from the Dedekind complementary module to
the `A`-linear dual of `B`. -/
noncomputable def dedekindComparison :
    Submodule.dedekindComplementary A (FractionRing A) B
        (B ⊗[A] FractionRing A) →ₗ[B] Module.Dual A B where
  toFun := dedekindTraceFunctional A B
  map_add' := dedekindTraceFunctional_add A B
  map_smul' := dedekindTraceFunctional_smul A B

/-- The comparison map evaluates by the trace pairing after mapping its value to
`FractionRing A`. -/
theorem dedekindComparison_apply
    (x : Submodule.dedekindComplementary A (FractionRing A) B
      (B ⊗[A] FractionRing A)) (b : B) :
    algebraMap A (FractionRing A) (dedekindComparison A B x b) =
      Algebra.trace (FractionRing A) (B ⊗[A] FractionRing A)
        (algebraMap B (B ⊗[A] FractionRing A) b * x) := sorry

section ComparisonBijective

variable {A B}
variable [h_noetherian : IsNoetherianRing A] [h_finite : Module.Finite A B]
variable
  (h_regular : ∀ a ∈ nonZeroDivisors A,
    algebraMap A B a ∈ nonZeroDivisors B)
variable
  [h_etale : Algebra.Etale (FractionRing A) (B ⊗[A] FractionRing A)]

include h_noetherian h_finite h_regular h_etale

/-- If `A` is noetherian, `B` is finite over `A`, non-zero-divisors of `A`
remain non-zero-divisors in `B`, and the generic fibre is etale, then the
canonical trace-pairing comparison is bijective. -/
theorem dedekindComparison_bijective :
    Function.Bijective (dedekindComparison A B) := sorry

end ComparisonBijective

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [h_noetherian_A : IsNoetherianRing A] [h_noetherian_B : IsNoetherianRing B]
variable [h_finite : Module.Finite A B] [h_flat : Module.Flat A B]
variable (h_regular : ∀ a ∈ nonZeroDivisors A,
  algebraMap A B a ∈ nonZeroDivisors B)
variable [h_etale : Algebra.Etale (FractionRing A) (B ⊗[A] FractionRing A)]

include h_noetherian_A h_noetherian_B h_finite h_flat h_regular h_etale

/-- For a finite flat map with etale generic fibre, the canonical comparison
map sends the canonical complementary element to the finite-flat trace element. -/
theorem dedekindComparison_one_eq_traceElement :
    let one : Submodule.dedekindComplementary A (FractionRing A) B
        (B ⊗[A] FractionRing A) :=
      ⟨1, (_root_.dedekindTrace_mem_base_iff_one_mem_complementary
        (A := A) (B := B) h_regular).mp
        (_root_.dedekindTrace_mem_base_of_flat (A := A) (B := B) h_regular)⟩
    (dedekindComparison A B one) ⊗ₜ[B] (1 : B) =
      finiteFlatTraceElement A B := sorry

/-- An element lies in the fractional Dedekind different exactly when its
scalar action carries the relative dualizing module into the trace-element span. -/
theorem mem_dedekindDifferent_iff_smul_mem_span (b : B) :
    algebraMap B (B ⊗[A] FractionRing A) b ∈
        Submodule.dedekindDifferent A (FractionRing A) B
          (B ⊗[A] FractionRing A) ↔
      ∀ ω : RelativeDualizingModule.of A B B (.of_moduleFinite) inferInstance,
        b • ω ∈ Submodule.span B {finiteFlatTraceElement A B} := sorry

end Algebra.RelativeDualizingModule
