module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Algebraization
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Lemma 76.42.8: on a Noetherian algebraic space X over a scheme S, with a
quasi-coherent ideal I, a morphism α from an object of Coh(X, I) to the
completion of a coherent module G whose kernel and cokernel are annihilated by
a power of I algebraizes uniquely up to unique isomorphism to a coherent module
F, a map a : F ⟶ G of the same torsion type, and an isomorphism
β : (F_n) ≅ F^∧ with α = a^∧ ∘ β. -/
@[stacks 08BB] #check
  (AlgebraicGeometry.AlgebraicSpace.CoherentCompletion.existsUnique_algebraization_to :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
      {I : IdealSubobject X} [IsQuasiCoherent I]
      (E : CoherentFormalModules X I) (G : Coh X)
      (alpha : E ⟶ (CoherentCompletion.functor I).obj G),
      CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation I alpha →
        ∃ z : FormalMapToCompletionAlgebraization E G alpha,
          ∀ z' : FormalMapToCompletionAlgebraization E G alpha,
            ∃! e : z.F ≅ z'.F,
              FormalMapToCompletionAlgebraization.IsomorphismCompatible z z' e)
