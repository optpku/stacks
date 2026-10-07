module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.PuncturedStalk.FiniteFamily.Equivalence

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FinitePresentationIsoOverOpen

/- Lemma 54.6.1: base change at a finite nonempty family of distinct closed points is an
equivalence between finite-presentation morphisms with the prescribed open isomorphism and the
corresponding family of punctured-stalk objects. -/
@[stacks 0BFV] #check (AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChangeIsEquivalence :
    ∀ {ι : Type u} [Finite ι] [Nonempty ι]
      (S : Scheme.{u}) (s : ι → S)
      (hs_closed : ∀ i, s i ∈ closedPoints S)
      (hs_pairwise : Function.Injective s)
      (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι],
      Functor.IsEquivalence
        (puncturedStalkBaseChange S s hs_closed hs_pairwise U hU))

end AlgebraicGeometry.FinitePresentationIsoOverOpen
