/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.SheafEquivalence
public import Mathlib.AlgebraicGeometry.Modules.Presheaf

@[expose] public section

open CategoryTheory
open scoped TopCat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The structure sheaf of `S`, transported to its small Zariski site. -/
noncomputable def smallZariskiRingSheaf (S : Scheme.{u}) :
    Sheaf S.smallZariskiTopology RingCat.{u} :=
  (smallZariskiSheafEquiv S RingCat.{u}).inverse.obj S.ringCatSheaf

/-- The transported small-Zariski ring sheaf is the inverse image of the structure sheaf under
the canonical sheaf equivalence. -/
theorem smallZariskiRingSheaf_def (S : Scheme.{u}) :
    smallZariskiRingSheaf S =
      (smallZariskiSheafEquiv S RingCat.{u}).inverse.obj S.ringCatSheaf := sorry

/-- The small Zariski site of `S`, equipped with its transported structure sheaf. -/
abbrev smallZariskiRingedSite (S : Scheme.{u}) : RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf S.smallZariskiTopology (smallZariskiRingSheaf S)

/-- The structure sheaf of the small-Zariski ringed site is the transported ring sheaf. -/
theorem smallZariskiRingedSite_structureSheaf (S : Scheme.{u}) :
    (smallZariskiRingedSite S).structureSheaf = smallZariskiRingSheaf S := sorry

/-- The canonical functor from opens to the small Zariski site is a morphism of sites. -/
instance smallZariskiOpenFunctor_isMorphismOfSites (S : Scheme.{u}) :
    IsMorphismOfSites (Opens.grothendieckTopology (S : TopCat))
      S.smallZariskiTopology (smallZariskiOpenFunctor S) := sorry

/-- The canonical comparison from the small-Zariski ringed site of `S` to the ringed site of
opens of its underlying ringed space. -/
noncomputable def smallZariskiRingedSiteHom (S : Scheme.{u}) :
    RingedSite.Hom (smallZariskiRingedSite S)
      (RingedSpace.opensRingedSite S.toRingedSpace) where
  base := smallZariskiOpenFunctor S
  isMorphismOfSites := smallZariskiOpenFunctor_isMorphismOfSites S
  structureSheafMap :=
    (smallZariskiSheafEquiv S RingCat.{u}).counitInv.app S.ringCatSheaf

/-- The base of the small-Zariski ringed-site comparison is the canonical functor from opens. -/
theorem smallZariskiRingedSiteHom_base (S : Scheme.{u}) :
    (smallZariskiRingedSiteHom S).base = smallZariskiOpenFunctor S := sorry

/-- The structure-sheaf map of the small-Zariski comparison is the counit inverse of the
canonical equivalence of sheaf categories. -/
theorem smallZariskiRingedSiteHom_structureSheafMap (S : Scheme.{u}) :
    (smallZariskiRingedSiteHom S).structureSheafMap =
      (smallZariskiSheafEquiv S RingCat.{u}).counitInv.app S.ringCatSheaf := sorry

/-- The canonical comparison between the small-Zariski and opens ringed sites is a ringed
equivalence. -/
instance smallZariskiRingedSiteHom_isRingedEquivalence (S : Scheme.{u}) :
    (smallZariskiRingedSiteHom S).IsRingedEquivalence := sorry

end AlgebraicGeometry.Scheme
