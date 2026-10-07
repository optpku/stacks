module

import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 30.23.6 (1): a morphism from a coherent formal module to the completion of a
coherent module whose stagewise kernel and cokernel are uniformly annihilated by an ideal power
has an algebraization, unique up to a unique compatible isomorphism. -/
@[stacks 0889] #check
  (Scheme.CoherentCompletion.existsUnique_algebraization_to :
    ∀ {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
      (E : Scheme.CoherentFormalModules X I)
      (G : RingedSpace.Coh X.toRingedSpace)
      (alpha : E ⟶ (Scheme.CoherentCompletion.functor I).obj G)
      (_ : Scheme.CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation
        I alpha),
      ∃ z : Scheme.FormalMapToCompletionAlgebraization
          (CoherentCompletionFunctor.canonical X I) E G alpha,
        ∀ z' : Scheme.FormalMapToCompletionAlgebraization
            (CoherentCompletionFunctor.canonical X I) E G alpha,
          ∃! e : z.F ≅ z'.F,
            Scheme.FormalMapToCompletionAlgebraization.IsomorphismCompatible z z' e)

/- Lemma 30.23.6 (2): a morphism from the completion of a coherent module to a coherent
formal module whose stagewise kernel and cokernel are uniformly annihilated by an ideal power
has an algebraization, unique up to a unique compatible isomorphism. -/
@[stacks 0889] #check
  (Scheme.CoherentCompletion.existsUnique_algebraization_from :
    ∀ {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
      (G : RingedSpace.Coh X.toRingedSpace)
      (E : Scheme.CoherentFormalModules X I)
      (alpha : (Scheme.CoherentCompletion.functor I).obj G ⟶ E)
      (_ : Scheme.CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation
        I alpha),
      ∃ z : Scheme.CompletionToFormalMapAlgebraization
          (CoherentCompletionFunctor.canonical X I) G E alpha,
        ∀ z' : Scheme.CompletionToFormalMapAlgebraization
            (CoherentCompletionFunctor.canonical X I) G E alpha,
          ∃! e : z.F ≅ z'.F,
            Scheme.CompletionToFormalMapAlgebraization.IsomorphismCompatible z z' e)
