module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal.Proper
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 33.10.7: for a proper geometrically normal scheme `X` over a field `k`, bijectivity of
the canonical map `k → Γ(X, 𝒪_X)`, geometric connectedness, geometric irreducibility, and
geometric integrality are equivalent. -/
@[stacks 0FD3] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyNormal.proper_globalSections_tfae :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom],
      AlgebraicGeometry.SchemeOverField.geometricallyNormal X →
        List.TFAE
          [ Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)
          , GeometricallyConnected X.hom
          , GeometricallyIrreducible X.hom
          , GeometricallyIntegral X.hom
          ])
