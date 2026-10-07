module

public import stacks_project.Chap90.Lemma_90_4_5_Residue
public import stacks_project.Chap90.Lemma_90_9_3
public import stacks_project.Chap90.«90_3_10_3_Comparison»

/-!
# Existence of a smooth object of `Ĉ_Λ` with canonical cotangent identifications

There exists `R` in `CompleteLocalAlgCat Λ k` satisfying the equivalent conditions
of Lemma 90.9.3, such that the canonical Jacobi–Zariski maps identify
`H1Cotangent Λ k` with `m_R / m_R²` and `k ⊗[R] Ω[R⁄Λ]` with `Ω[k⁄Λ]`.
-/

@[expose] public section

open CategoryTheory IsLocalRing Algebra.H1Cotangent KaehlerDifferential
open scoped TensorProduct

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- The canonical residue map of an object of `Ĉ_Λ` is surjective. -/
theorem algebraMap_surjective (R : CompleteLocalAlgCat Λ k) :
    Function.Surjective (algebraMap R.carrier k) :=
  sorry

/-- The kernel of the residue map of an object of `Ĉ_Λ` is the maximal ideal. -/
theorem ker_algebraMap_eq_maximalIdeal (R : CompleteLocalAlgCat Λ k) :
    RingHom.ker (algebraMap R.carrier k) = maximalIdeal R.carrier :=
  sorry

/-- Lemma 90.9.5: there exists `R` in `Ob(Ĉ_Λ)` such that the equivalent
conditions of Lemma 90.9.3 hold, represented here by `m_R`-adic formal
smoothness of `algebraMap Λ R.carrier`, and moreover the canonical
Jacobi–Zariski maps identify `H1Cotangent Λ k` with `m_R / m_R²` and
`k ⊗[R] Ω[R⁄Λ]` with `Ω[k⁄Λ]`. -/
@[stacks 06SM]
theorem exists_formallySmooth_h1Cotangent_mapBaseChange :
    ∃ R : CompleteLocalAlgCat Λ k,
      (algebraMap Λ R.carrier).formally_smooth_for_adic (maximalIdeal R.carrier) ∧
        Function.Bijective (toKerCotangent Λ R.carrier k (algebraMap_surjective R)) ∧
        Function.Bijective (mapBaseChange Λ R.carrier k) :=
  sorry

/-- Existence of `R` in `CompleteLocalAlgCat Λ k` such that
`underline R |_{C_Λ}` is smooth and the canonical Jacobi–Zariski maps
identify `H1Cotangent Λ k` with `m_R / m_R²` and `k ⊗[R] Ω[R⁄Λ]` with
`Ω[k⁄Λ]`. -/
theorem exists_isSmooth_h1Cotangent_mapBaseChange :
    ∃ R : CompleteLocalAlgCat Λ k,
      Functor.IsSmooth (CategoryOfElements.π (restrictedCoyoneda R)) ∧
        Function.Bijective (toKerCotangent Λ R.carrier k (algebraMap_surjective R)) ∧
        Function.Bijective (mapBaseChange Λ R.carrier k) :=
  sorry

end CompleteLocalAlgCat
