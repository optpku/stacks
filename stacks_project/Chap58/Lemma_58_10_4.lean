/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.PuncturedSpectrum
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 58.10.4: if `U` is a dense quasi-compact open in a scheme `X`, every
point of `X \ U` is closed, and the punctured spectrum of every strict
henselization of `𝒪_{X, x}` is connected for `x ∉ U`, then the restriction
functor `finiteEtaleBaseChange U.ι : FiniteEtale X ⥤ FiniteEtale U` is fully
faithful. -/
@[stacks 0BSA] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChange_fullyFaithful_of_denseQuasiCompactLocallyConnected :
    ∀ {X : Scheme.{u}} (U : X.Opens) [QuasiCompact U.ι],
      Dense (U : Set X) →
        (∀ x : X, x ∉ U → IsClosed ({x} : Set X)) →
          (∀ (x : X) (hx : x ∉ U) (Ash : Type u) [CommRing Ash]
            [Algebra (X.presheaf.stalk x) Ash]
            [IsStrictHenselizationOf (X.presheaf.stalk x) Ash],
            ConnectedSpace (PuncturedSpectrum.scheme Ash)) →
            Nonempty (finiteEtaleBaseChange U.ι).FullyFaithful)

end AlgebraicGeometry.Scheme
