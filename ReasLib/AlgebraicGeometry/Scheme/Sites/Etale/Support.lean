module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction
public import ReasLib.Topology.Sheaf.Support

/-!
# Supports of sheaves on the small étale site

This module transports a small étale sheaf of rings to the underlying topological space of a
scheme and records the closedness of its support.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- A sheaf on the small étale site restricts to the small Zariski site and hence
corresponds to a presheaf on the underlying topological space of the scheme. -/
noncomputable def etaleRingSheafOnSpace
    (S : Scheme.{u}) (F : Sheaf S.smallEtaleTopology RingCat.{u}) :
    TopCat.Sheaf RingCat.{u} (S.toPresheafedSpace : TopCat) :=
  ⟨((Scheme.smallZariskiOpenFunctor S ⋙
      Scheme.SiteRestriction.smallZariskiToSmallEtale S).op ⋙ F.1), sorry⟩

/-- The support of a sheaf of rings on the small étale site, transported to the
underlying topological space of the scheme. -/
noncomputable abbrev etaleRingSheafSupport
    (S : Scheme.{u}) (F : Sheaf S.smallEtaleTopology RingCat.{u}) : Set S :=
  TopCat.Sheaf.ringSheafSupport (etaleRingSheafOnSpace S F)

/-- The support of a sheaf of rings on the small étale site is closed. -/
theorem isClosed_etaleRingSheafSupport
    (S : Scheme.{u}) (F : Sheaf S.smallEtaleTopology RingCat.{u}) :
    IsClosed (etaleRingSheafSupport S F) := sorry

end AlgebraicGeometry.Scheme.Etale
