module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Affine.Pullback

/-!
# Topological invariance of affine étale sites

Universal homeomorphisms induce equivalences on affine étale sites.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.AffineEtale

/-- Pullback along a universal homeomorphism is an equivalence on affine étale sites. -/
instance pullback_isEquivalence_of_universalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f] :
    (pullback f).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.AffineEtale
