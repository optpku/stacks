module

public import Mathlib.Topology.Sheaves.Stalks
public import ReasLib.Topology.Opens.Point
public import ReasLib.CategoryTheory.Sites.Point.Enough
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Picard
public import ReasLib.AlgebraicGeometry.RingedSpace.LocallyRinged
public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged.Point
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Picard.Cohomology

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open SheafOfModules.RingedSite
open scoped RingedSpacePicard

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.6.1:
- primary domain: units sheaves and Picard groups of ringed spaces, with the source statement
  comparing `H¹(X, 𝒪_Xˣ)` to the Picard group of `X`;
- sampled owner declarations:
  `Pic(X)`,
  `Sheaf.IsLocallyRinged`,
  `SheafOfModules.RingedSite.PicardGroup`,
  `CategoryTheory.Sheaf.unitsAddSheaf`,
  `ringedSiteUnitsSheaf_H1_equiv_picardGroup`,
  `RingedSpace.StalkLocalRing.localUnitDichotomy`,
  `Sheaf.nontrivialityMap_isIso_iff_stalk_nontrivial`;
- best owner abstraction: the canonical owner theorem is the ringed-site comparison
  `ringedSiteUnitsSheaf_H1_equiv_picardGroup`, and the Chapter 20 item should be only its
  ringed-space specialization between `CategoryTheory.Sheaf.unitsAddSheaf X.sheaf` and `Pic(X)`,
  with the Chapter 17 stalk-local-ring bridge feeding the Chapter 18 owner
  `Sheaf.IsLocallyRinged`, rather than keeping the local-unit and equalizer clauses as parallel ad
  hoc data in the main declaration;
- primitive data: the ringed space `X` and the source-facing stalkwise local-ring hypothesis;
- derived API: the degree-`1` cohomology group of the units sheaf and the ringed-space Picard
  group `Pic(X)`, compared by a theorem-level bijective additive map.

Source/core/bridge triage:
- `source-facing`: the ringed-space comparison `H¹(X, 𝒪_Xˣ) ≃ Pic(X)` under
  stalkwise local-ring hypotheses;
- `core/canonical`: `ringedSiteUnitsSheaf_H1_equiv_picardGroup`,
  `CategoryTheory.Sheaf.unitsAddSheaf`, `SheafOfModules.RingedSite.PicardGroup`,
  `Sheaf.IsLocallyRinged`,
  `RingedSpace.StalkLocalRing.localUnitDichotomy`, and
  `Sheaf.nontrivialityMap_isIso_iff_stalk_nontrivial`;
- `bridge/view`: specialization of the ringed-site owners to the structure sheaf `X.sheaf`.
-/

/-- Lemma 20.6.1: if all stalks of the structure sheaf of a ringed space are local rings, then
there exists a bijective additive comparison map from the first cohomology of the units sheaf
`𝒪_Xˣ` to the Picard group of `X`. This is the ringed-space specialization of the
theorem-level Chapter 21 owner `ringedSiteUnitsSheaf_H1_equiv_picardGroup`. -/
@[stacks 09NU]
theorem unitsSheaf_H1_equiv_picardGroup_of_stalk_isLocalRing
    (X : RingedSpace)
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x))
    [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat)]
    [(Opens.grothendieckTopology X).HasSheafCompose (forget AddCommGrpCat)]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
    [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]
    [MonoidalCategory (Modules X)] [SymmetricCategory (Modules X)]
    -- The Chapter 21 owner `ringedSiteUnitsSheaf_H1_equiv_picardGroup` requires the ambient tensor
    -- unit of the ring sheaf to be the sheafified unit. Under pinned Mathlib this is not an active
    -- instance for a ringed space's structure sheaf, so we carry it as a hypothesis exactly as the
    -- sibling items (`Chap17.Definition_17_23_1`, `Chap20.Lemma_20_55_3/5/6`) do.
    [SheafOfModules.UnitIsSheafifiedUnit (RingedSpace.ringCatSheaf X)] :
    ∃ e : ((CategoryTheory.Sheaf.unitsAddSheaf X.sheaf).H 1) →+ Pic(X),
      Function.Bijective e := sorry

end AlgebraicGeometry.RingedSpace
