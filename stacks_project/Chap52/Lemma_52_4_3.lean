/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalCohomology.PolynomialModuleLift
import StacksCheckRecall

@[expose] public section

noncomputable section

open scoped BigOperators

universe u v w

/- Lemma 52.4.3 (1): after increasing the exponent and restricting the coefficient maps, every
finite module over a Noetherian algebra has a unique compatible graded polynomial-module lift. -/
@[stacks 0EIC] #check
  (Ideal.LocalCohomology.existsUniqueGradedPolynomialModuleLift :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ} (I : Ideal A)
      (f : Fin r → I)
      (hgen : Ideal.span (Set.range fun j ↦ (f j : A)) = I)
      (hcd : Ideal.LocalCohomology.dimension I I.fg_of_isNoetherianRing = 1)
      {c : ℕ} (hc : 1 ≤ c) (φ : Fin r → I.powerHom A c)
      (hφ : ∑ j, (f j : A) • φ j = (I ^ c).subtype)
      {B : Type v} [CommRing B] [IsNoetherianRing B] (α : A →+* B)
      (N : Type w) [AddCommGroup N] [Module B N] [Module.Finite B N],
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
              Ideal.LocalCohomology.IsPolynomialModuleLift I α Φ ΦN)

/- Lemma 52.4.3 (2): evaluation of any compatible graded polynomial-module lift is the canonical
inclusion from the powered Rees module into the Rees module of the original ideal. -/
@[stacks 0EIC] #check
  (Ideal.LocalCohomology.polynomialModuleLift_comp_evaluation :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ} (I : Ideal A)
      (f : Fin r → I)
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
      (hΦN : Ideal.LocalCohomology.IsPolynomialModuleLift I α Φ ΦN),
      (MvPolynomial.GradedModule.evaluation (I.map α)
          (fun j ↦ Ideal.ReesModule.mappedGenerator I α (f j))).comp
          (GradedModule.MapsTo.toLinearMap ΦN) =
        GradedModule.MapsTo.toLinearMap
          (Ideal.ReesModule.powerInclusion (I.map α) N hc))
