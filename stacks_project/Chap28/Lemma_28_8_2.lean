module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 28.8.2: for a scheme `X`, Cohen-Macaulayness is equivalent to local Noetherianity
together with Cohen-Macaulayness of every stalk, and equivalently it suffices to test the stalks
at closed points. -/
@[stacks 02IP] #check
  (AlgebraicGeometry.Scheme.cohenMacaulay_tfae_stalk_and_closedPointStalk :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      List.TFAE
        [ AlgebraicGeometry.Scheme.CohenMacaulay X
        , AlgebraicGeometry.IsLocallyNoetherian X ∧
            ∀ x : X, CohenMacaulayRing (X.presheaf.stalk x)
        , AlgebraicGeometry.IsLocallyNoetherian X ∧
            ∀ x : X, x ∈ closedPoints X →
              CohenMacaulayRing (X.presheaf.stalk x)
        ])
