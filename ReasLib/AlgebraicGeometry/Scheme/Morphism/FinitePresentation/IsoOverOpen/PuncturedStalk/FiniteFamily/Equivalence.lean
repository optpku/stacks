module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.PuncturedStalk.FiniteFamily

open CategoryTheory
open scoped AlgebraicGeometry

universe u

@[expose] public section

namespace AlgebraicGeometry.FinitePresentationIsoOverOpen

/-- Base change at a finite nonempty family of distinct closed points is an equivalence between
finite-presentation morphisms with the prescribed open isomorphism and the corresponding family
of punctured-stalk objects. -/
instance puncturedStalkBaseChangeIsEquivalence
    {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι] :
    Functor.IsEquivalence
      (puncturedStalkBaseChange S s hs_closed hs_pairwise U hU) := sorry

end AlgebraicGeometry.FinitePresentationIsoOverOpen

end
