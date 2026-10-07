module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.PuncturedStalk.FiniteFamily

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- 54.6.0.1: Base change from finitely presented `S`-schemes that are isomorphisms away from
a finite nonempty family of distinct closed points to the corresponding family of punctured
local schemes defines a functor `F`. -/
@[stacks 0BFU] #check
  (AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange :
    ∀ {ι : Type u} [Finite ι] [Nonempty ι]
      (S : Scheme.{u}) (s : ι → S)
      (hs_closed : ∀ i, s i ∈ closedPoints S)
      (hs_pairwise : Function.Injective s)
      (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι],
      FinitePresentationIsoOverOpen U ⥤
        ((i : ι) → FinitePresentationIsoOverOpen
          (PuncturedSpectrum.puncturedOpen (S.presheaf.stalk (s i)))))
