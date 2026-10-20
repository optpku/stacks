module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CommRingedHom

open AlgebraicGeometry CategoryTheory

universe u

/- The commutative small-étale ringed-site morphism associated to a scheme morphism. -/
#check (Scheme.Etale.Small.commRingedHom :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
    RingedSite.Hom (Scheme.AssociatedModule.smallCommRingedSite .etale X)
      (Scheme.AssociatedModule.smallCommRingedSite .etale Y))
