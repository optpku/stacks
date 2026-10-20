module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Purity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped ENat

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 58.26.3: if `f : X ⟶ S` is smooth, `S` is Noetherian, `U ⊂ X` is open,
the scheme-theoretic fibers satisfy `X_s = U_s` whenever the local ring at `s`
has depth at most `1`,
and `U_s` is dense in `X_s` for every `s`, then restriction
`FÉt_X ⥤ FÉt_U` along `U.ι` is an equivalence. -/
@[stacks 0EYB] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChange_isEquivalence_of_smoothNoetherianFiberDensity :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsNoetherian S] (U : X.Opens)
    (h_eq : ∀ s : S,
      moduleDepth (S.presheaf.stalk s) (S.presheaf.stalk s) ≤ (1 : ℕ∞) →
        f.fiberι s ⁻¹ᵁ U = ⊤)
    (h_dense : ∀ s : S, Dense (f.fiberι s ⁻¹ᵁ U : Set (f.fiber s))),
    Functor.IsEquivalence (finiteEtaleBaseChange U.ι))

end AlgebraicGeometry.Scheme
