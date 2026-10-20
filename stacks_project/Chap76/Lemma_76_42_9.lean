/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Algebraization.Thickening
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

universe u

/- Lemma 76.42.9: in Situation 76.42.5, if 𝒦 ⊂ 𝒪_X is a quasi-coherent sheaf
of ideals, every positive-power 𝒦-thickening X_e has an equivalence
Coh_support proper over A(𝒪_{X_e}) ⥤ Coh_support proper over A(X_e, ℐ_e),
and a coherent module ℋ with support proper over A approximates (ℱ_n) by a
map α : (ℱ_n) ⟶ ℋ^∧ whose kernel and cokernel are annihilated by a power of
𝒦, then (ℱ_n) lies in the essential image of 76.42.5.1. -/
@[stacks 08BC] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.mem_essImage_of_thickening_equivalences_and_torsion_approximation :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (I : Ideal A) [IsAdicComplete I A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      [FiniteType (SchemeRealization.toBase X)] [Separated (SchemeRealization.toBase X)]
      (K : IdealSubobject X) [IsQuasiCoherent K],
      (∀ e : ℕ+,
        (idealPowerCompletionFunctor (SchemeRealization.toBase X)
          (pullbackIdeal I (SchemeRealization.toBase X)) K e).IsEquivalence) →
      (E : CoherentFormalProperSupportOver (SchemeRealization.toBase X)
        (pullbackIdeal I (SchemeRealization.toBase X))) →
      (H : CoherentProperSupportOver (SchemeRealization.toBase X)) →
      (alpha : E ⟶
        (coherentProperSupportCompletionFunctor (SchemeRealization.toBase X)
          (pullbackIdeal I (SchemeRealization.toBase X))).obj H) →
      CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation K alpha.hom →
      (coherentProperSupportCompletionFunctor (SchemeRealization.toBase X)
        (pullbackIdeal I (SchemeRealization.toBase X))).essImage E)
