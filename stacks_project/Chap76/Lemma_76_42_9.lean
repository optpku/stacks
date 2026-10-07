module

public import stacks_project.Chap76.Lemma_76_42_9_Algebraization
public import stacks_project.Chap76.Lemma_76_42_9_Thickening
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
  (mem_essImage_of_thickening_equivalences_and_torsion_approximation :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (I : Ideal A) [IsAdicComplete I A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      [FiniteType (toBase X)] [Separated (toBase X)]
      (K : IdealSubobject X) [IsQuasiCoherent K],
      (∀ e : ℕ+,
        (idealPowerCompletionFunctor (toBase X)
            (pullbackIdeal I (toBase X)) K e).IsEquivalence) →
      (E : CoherentFormalProperSupportOver (toBase X)
        (pullbackIdeal I (toBase X))) →
      (H : CoherentProperSupportOver (toBase X)) →
      (alpha :
        E ⟶
          (coherentProperSupportCompletionFunctor (toBase X)
              (pullbackIdeal I (toBase X))).obj H) →
      CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation K
          alpha.hom →
      (coherentProperSupportCompletionFunctor (toBase X)
          (pullbackIdeal I (toBase X))).essImage E)
