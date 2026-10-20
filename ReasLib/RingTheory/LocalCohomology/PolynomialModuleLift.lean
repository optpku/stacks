module

public import ReasLib.Algebra.Module.Rees
public import ReasLib.RingTheory.MvPolynomial.GradedModule
public import ReasLib.RingTheory.ReesAlgebra.Grading.PowerInclusion

@[expose] public section

noncomputable section

open scoped BigOperators TensorProduct

universe u v w

namespace Ideal.LocalCohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- Mapping coefficients along `α` preserves the degree of the image under a graded polynomial
lift. -/
theorem mapPolynomialLift_mem_grade {r n c : ℕ} (I : Ideal A)
    {B : Type v} [CommRing B] (α : A →+* B)
    (Φ : ReesAlgebra.Grading.grade (I ^ c) →ₐᵍ[A]
      MvPolynomial.standardGrading (Fin r) A)
    (g : (I ^ (n * c) : Ideal A)) :
    MvPolynomial.map α
        (Φ (ReesAlgebra.Grading.linear (I ^ c) n
          (Ideal.ReesModule.powerCoefficient I g))) ∈
      MvPolynomial.standardGrading (Fin r) B n := sorry

/-- A graded map on a powered Rees module has the coefficientwise formula induced by `Φ`. -/
def IsPolynomialModuleLift {r c : ℕ} (I : Ideal A)
    {B : Type v} [CommRing B] (α : A →+* B)
    {N : Type w} [AddCommGroup N] [Module B N]
    (Φ : ReesAlgebra.Grading.grade (I ^ c) →ₐᵍ[A]
      MvPolynomial.standardGrading (Fin r) A)
    (ΦN : GradedModule.MapsTo B
      (Ideal.ReesModule.grade ((I.map α) ^ c) N)
      (MvPolynomial.GradedModule.grade (Fin r) B N) id) : Prop :=
  ∀ (n : ℕ) (g : (I ^ (n * c) : Ideal A)) (x : N),
    GradedModule.MapsTo.toLinearMap ΦN (Ideal.ReesModule.mappedOf I α g x) =
      MvPolynomial.GradedModule.of (Fin r) B N n
        (⟨MvPolynomial.map α
            (Φ (ReesAlgebra.Grading.linear (I ^ c) n
              (Ideal.ReesModule.powerCoefficient I g))),
          mapPolynomialLift_mem_grade I α Φ g⟩ ⊗ₜ[B] x)

/-- The polynomial-module lift predicate is exactly its formula on homogeneous products. -/
theorem isPolynomialModuleLift_iff {r c : ℕ} (I : Ideal A)
    {B : Type v} [CommRing B] (α : A →+* B)
    {N : Type w} [AddCommGroup N] [Module B N]
    (Φ : ReesAlgebra.Grading.grade (I ^ c) →ₐᵍ[A]
      MvPolynomial.standardGrading (Fin r) A)
    (ΦN : GradedModule.MapsTo B
      (Ideal.ReesModule.grade ((I.map α) ^ c) N)
      (MvPolynomial.GradedModule.grade (Fin r) B N) id) :
    IsPolynomialModuleLift I α Φ ΦN ↔
      ∀ (n : ℕ) (g : (I ^ (n * c) : Ideal A)) (x : N),
        GradedModule.MapsTo.toLinearMap ΦN (Ideal.ReesModule.mappedOf I α g x) =
          MvPolynomial.GradedModule.of (Fin r) B N n
            (⟨MvPolynomial.map α
                (Φ (ReesAlgebra.Grading.linear (I ^ c) n
                  (Ideal.ReesModule.powerCoefficient I g))),
              mapPolynomialLift_mem_grade I α Φ g⟩ ⊗ₜ[B] x) := sorry

/-- After increasing the exponent and restricting the coefficient maps, a finite module over a
Noetherian algebra has a unique graded polynomial-module lift. -/
theorem existsUniqueGradedPolynomialModuleLift {r : ℕ} (I : Ideal A) (f : Fin r → I)
    (hgen : Ideal.span (Set.range fun j ↦ (f j : A)) = I)
    (hcd : dimension I I.fg_of_isNoetherianRing = 1)
    {c : ℕ} (hc : 1 ≤ c) (φ : Fin r → I.powerHom A c)
    (hφ : ∑ j, (f j : A) • φ j = (I ^ c).subtype)
    {B : Type v} [CommRing B] [IsNoetherianRing B] (α : A →+* B)
    (N : Type w) [AddCommGroup N] [Module B N] [Module.Finite B N] :
    ∃ (c' : ℕ) (hcc : c ≤ c') (hc' : 1 ≤ c'),
      ∃ φ' : Fin r → I.powerHom A c',
        (∀ j, φ' j = (φ j).comp
          (Submodule.inclusion (Ideal.pow_le_pow_right hcc))) ∧
        (∑ j, (f j : A) • φ' j = (I ^ c').subtype) ∧
        ∃ Φ : ReesAlgebra.Grading.grade (I ^ c') →ₐᵍ[A]
            MvPolynomial.standardGrading (Fin r) A,
          (∀ g : (I ^ c' : Ideal A),
            Φ (ReesAlgebra.Grading.degreeOne (I ^ c') g) =
              ∑ j, MvPolynomial.C (φ' j g) * MvPolynomial.X j) ∧
          (ReesAlgebra.Presentation.toRees f).comp Φ.toAlgHom =
            (ReesAlgebra.Grading.powerInclusion I hc').toAlgHom ∧
          ∃! ΦN : GradedModule.MapsTo B
              (Ideal.ReesModule.grade ((I.map α) ^ c') N)
              (MvPolynomial.GradedModule.grade (Fin r) B N) id,
            IsPolynomialModuleLift I α Φ ΦN := sorry

/-- Evaluation of a polynomial-module lift is the canonical inclusion into the Rees module. -/
theorem polynomialModuleLift_comp_evaluation {r : ℕ} (I : Ideal A) (f : Fin r → I)
    {B : Type v} [CommRing B] (α : A →+* B)
    {N : Type w} [AddCommGroup N] [Module B N]
    {c : ℕ} (hc : 1 ≤ c)
    (Φ : ReesAlgebra.Grading.grade (I ^ c) →ₐᵍ[A]
      MvPolynomial.standardGrading (Fin r) A)
    (hΦ : (ReesAlgebra.Presentation.toRees f).comp Φ.toAlgHom =
      (ReesAlgebra.Grading.powerInclusion I hc).toAlgHom)
    (ΦN : GradedModule.MapsTo B
      (Ideal.ReesModule.grade ((I.map α) ^ c) N)
      (MvPolynomial.GradedModule.grade (Fin r) B N) id)
    (hΦN : IsPolynomialModuleLift I α Φ ΦN) :
    (MvPolynomial.GradedModule.evaluation (I.map α)
        (fun j ↦ Ideal.ReesModule.mappedGenerator I α (f j))).comp
        (GradedModule.MapsTo.toLinearMap ΦN) =
      GradedModule.MapsTo.toLinearMap
        (Ideal.ReesModule.powerInclusion (I.map α) N hc) := sorry

end Ideal.LocalCohomology
