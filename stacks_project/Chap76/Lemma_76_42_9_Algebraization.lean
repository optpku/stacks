module

public import Mathlib.CategoryTheory.EssentialImage
public import stacks_project.Chap76.Lemma_76_42_6_Hom
public import stacks_project.Chap76.Lemma_76_42_9_Thickening

/-!
# Algebraization of proper-support coherent formal modules via thickenings

This file records uniform kernel-and-cokernel annihilation for morphisms of
coherent formal modules, and an essential-image criterion for the restricted
completion functor of Situation 76.42.5.
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoherentFormalMap

/-- One positive power of an ideal sheaf annihilates the kernels and cokernels of
every positive stage of a morphism of coherent formal modules. -/
def StagesHaveUniformKernelCokernelAnnihilation
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
    [IsQuasiCoherent I] (K : IdealSubobject X)
    {F G : CoherentFormalModules X I} (alpha : F ⟶ G) : Prop :=
  ∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ+,
    idealPowerProductSubobject K
        (kernel ((Coh.inclusion X).map (alpha.hom.app (op (n : ℕ))))) t = ⊥ ∧
      idealPowerProductSubobject K
        (cokernel ((Coh.inclusion X).map (alpha.hom.app (op (n : ℕ))))) t = ⊥

/-- Unfold uniform kernel-and-cokernel annihilation across all positive
stages. -/
theorem stagesHaveUniformKernelCokernelAnnihilation_iff
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
    [IsQuasiCoherent I] (K : IdealSubobject X)
    {F G : CoherentFormalModules X I} (alpha : F ⟶ G) :
    StagesHaveUniformKernelCokernelAnnihilation K alpha ↔
      ∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ+,
        idealPowerProductSubobject K
            (kernel ((Coh.inclusion X).map (alpha.hom.app (op (n : ℕ))))) t = ⊥ ∧
          idealPowerProductSubobject K
            (cokernel ((Coh.inclusion X).map (alpha.hom.app (op (n : ℕ))))) t = ⊥ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CoherentFormalMap

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- If restricted completion is an equivalence on every positive-power
`K`-thickening and a proper-support coherent module approximates a coherent
formal module by a map whose stagewise kernel and cokernel are annihilated by
a power of `K`, then the formal module lies in the essential image of
restricted completion. -/
theorem mem_essImage_of_thickening_equivalences_and_torsion_approximation
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [FiniteType (toBase X)] [Separated (toBase X)]
    (K : IdealSubobject X) [IsQuasiCoherent K]
    (hThickeningEquiv :
      ∀ e : ℕ+,
        (idealPowerCompletionFunctor (toBase X)
            (pullbackIdeal I (toBase X)) K e).IsEquivalence)
    (E : CoherentFormalProperSupportOver (toBase X)
      (pullbackIdeal I (toBase X)))
    (H : CoherentProperSupportOver (toBase X))
    (alpha :
      E ⟶
        (coherentProperSupportCompletionFunctor (toBase X)
            (pullbackIdeal I (toBase X))).obj H)
    (halpha :
      CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation K
        alpha.hom) :
    (coherentProperSupportCompletionFunctor (toBase X)
        (pullbackIdeal I (toBase X))).essImage E :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
