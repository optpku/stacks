module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over.StalkGluing.FiniteFamily
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u

/- Lemma 32.20.5: for a nonempty finite family of pairwise distinct closed points whose open
complement is quasi-compact, finite-presentation schemes over the scheme are equivalent to
compatible finite-presentation schemes over the complement and the local schemes, compared over
their punctured stalk opens. -/
@[stacks 0E8Q] #check
  (AlgebraicGeometry.finitePresentationOver_equivalence_stalkFamilyGluing :
    ∀ {ι : Type u} [Finite ι] [Nonempty ι]
      (S : Scheme.{u}) (s : ι → S)
      (hs_closed : ∀ i, s i ∈ closedPoints S)
      (hs_pairwise : Function.Injective s)
      (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ)
      [QuasiCompact U.ι],
      Nonempty
        (FinitePresentationOver S ≌ finitePresentationStalkFamilyGluingCategory S U s))
