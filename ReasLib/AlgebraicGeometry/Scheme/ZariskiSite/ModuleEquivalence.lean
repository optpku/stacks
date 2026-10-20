module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Equivalence
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.RingedComparison

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- Pushforward along the canonical comparison from the small Zariski ringed site of a scheme
to the ringed site of its open subsets is an equivalence of module categories. -/
instance smallZariskiModulePushforward_isEquivalence (S : Scheme.{u}) :
    (smallZariskiRingedSiteHom S).modulePushforward.{u}.IsEquivalence := sorry

end AlgebraicGeometry.Scheme
