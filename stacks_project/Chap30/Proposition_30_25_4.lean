module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Proper
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Proposition 30.25.4: if `A` is Noetherian and `I`-adically complete and `f : X ⟶ Spec(A)` is
proper, then the coherent-completion functor `Coh(𝒪_X) ⥤ Coh(X, I 𝒪_X)` from (30.23.3.1)
is an equivalence. The explicit-argument marker preserves every quantified instance hypothesis
in the checked type. -/
@[stacks 088C] #check
  (@AlgebraicGeometry.Scheme.CoherentCompletion.functor_isEquivalence_of_isProper :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {X : Scheme.{u}} [IsNoetherian X]
      (I : Ideal A) [IsAdicComplete I A]
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f],
      (AlgebraicGeometry.Scheme.CoherentCompletion.functor
        ((AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec I).comap f)).IsEquivalence)
