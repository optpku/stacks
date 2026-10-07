module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.PuncturedSpectrum
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 58.10.5: if `U` is a dense open in a scheme `X`, every quasi-compact
open of `X` has finitely many irreducible components, and the punctured
spectrum of every strict henselization of `𝒪_{X, x}` is connected for
`x ∉ U`, then the restriction functor
`finiteEtaleBaseChange U.ι : FiniteEtale X ⥤ FiniteEtale U` is fully
faithful. -/
@[stacks 0BQG] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChange_fullyFaithful_of_denseFiniteComponents
    : ∀ {X : Scheme.{u}} [HasFiniteIrreducibleComponentsOnCompactOpens X] (U : X.Opens),
    Dense (U : Set X) →
      (∀ (x : X) (hx : x ∉ U) (Ash : Type u) [CommRing Ash]
        [Algebra (X.presheaf.stalk x) Ash]
        [IsStrictHenselizationOf (X.presheaf.stalk x) Ash],
        ConnectedSpace (PuncturedSpectrum.scheme Ash)) →
      Nonempty (finiteEtaleBaseChange U.ι).FullyFaithful)

end AlgebraicGeometry.Scheme
