module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SchemeLocalization

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
universe u

/- Equation 66.27.0.4: scheme morphisms are recovered from their algebraic-space maps. -/
#check (AlgebraicGeometry.AlgebraicSpace.ofOverPreimage :
  ∀ {S : Scheme.{u}} {U V : Over S}, (ofOver U ⟶ ofOver V) → (U ⟶ V))

/- Equation 66.27.0.4: localization at an étale scheme identifies the ringed sites. -/
#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalizationIso :
  ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S} {U : Over S}
    (f : ofOver U ⟶ Y) [Etale f],
    RingedSiteMap.Iso (smallEtaleTopology (ofOver U)) (structureSheaf (ofOver U))
      ((smallEtaleTopology Y).over (smallEtaleSite.mk f))
      ((structureSheaf Y).over (smallEtaleSite.mk f)))
