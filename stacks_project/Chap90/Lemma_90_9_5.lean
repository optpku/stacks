/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Smooth.Cotangent
import StacksCheckRecall

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

/- Lemma 90.9.5: there exists `R` in `Ob(Ĉ_Λ)` such that the equivalent
conditions of Lemma 90.9.3 hold, represented here by `m_R`-adic formal
smoothness of `algebraMap Λ R.carrier`, and moreover the canonical
Jacobi–Zariski maps identify `H1Cotangent Λ k` with `m_R / m_R²` and
`k ⊗[R] Ω[R⁄Λ]` with `Ω[k⁄Λ]`. -/
@[stacks 06SM] #check (CompleteLocalAlgCat.exists_formallySmooth_h1Cotangent_mapBaseChange :
    ∃ R : CompleteLocalAlgCat Λ k,
      (algebraMap Λ R.carrier).formally_smooth_for_adic (IsLocalRing.maximalIdeal R.carrier) ∧
        Function.Bijective
          (toKerCotangent Λ R.carrier k (CompleteLocalAlgCat.algebraMap_surjective R)) ∧
        Function.Bijective (mapBaseChange Λ R.carrier k))

#check (CompleteLocalAlgCat.exists_isSmooth_h1Cotangent_mapBaseChange :
    ∃ R : CompleteLocalAlgCat Λ k,
      Functor.IsSmooth (CategoryOfElements.π (CompleteLocalAlgCat.restrictedCoyoneda R)) ∧
        Function.Bijective
          (toKerCotangent Λ R.carrier k (CompleteLocalAlgCat.algebraMap_surjective R)) ∧
        Function.Bijective (mapBaseChange Λ R.carrier k))

#check (CompleteLocalAlgCat.algebraMap_surjective :
  ∀ R : CompleteLocalAlgCat Λ k, Function.Surjective (algebraMap R.carrier k))

variable (R : CompleteLocalAlgCat Λ k)

#check (IsLocalRing.ker_eq_maximalIdeal (algebraMap R.carrier k)
  (CompleteLocalAlgCat.algebraMap_surjective R) :
  RingHom.ker (algebraMap R.carrier k) = IsLocalRing.maximalIdeal R.carrier)
