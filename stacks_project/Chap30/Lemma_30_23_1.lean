module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Affine
public import Mathlib.Algebra.Module.GradedModule
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 30.23.1: if `X = Spec(A)` for a Noetherian ring `A` and `𝓘` is the quasi-coherent
ideal sheaf associated to `I`, then `Coh(X, 𝓘)` is equivalent to the category of finite modules
over the `I`-adic completion of `A`. -/
@[stacks 087W] #check
  (CategoryTheory.SequentialInverseSystem.AffineCoherentFormalModules.nonemptyEquivalence :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A),
      Nonempty
        (CategoryTheory.SequentialInverseSystem.AffineCoherentFormalModules A I ≌
          FGModuleCat (AdicCompletion I A)))
