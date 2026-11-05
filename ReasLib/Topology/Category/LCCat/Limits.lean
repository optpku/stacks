/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import Mathlib.Topology.Homeomorph.Lemmas
public import ReasLib.Topology.Category.LCCat.Objects
public import ReasLib.Topology.Category.TopCat.Limits.Compact

/-!
# Finite limits of Hausdorff locally compact spaces

The defining object property of `LCCat` is stable under pullbacks, and `LCCat` has a terminal
object. Consequently the canonical full subcategory has finite limits. Compactness of a pullback
is also exposed as an instance for later covering arguments.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace LCCat.property

/-- Hausdorff local compactness is invariant under isomorphisms in `TopCat`. -/
@[stacks 09WZ "Hausdorff locally compact spaces are closed under isomorphisms", instance]
instance isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms LCCat.property where
  of_iso e h := by
    letI := h.1
    letI := h.2
    exact ⟨(TopCat.homeoOfIso e).t2Space,
      (TopCat.homeoOfIso e).locallyCompactSpace_iff.mp inferInstance⟩

/-- A pullback of Hausdorff locally compact spaces in `TopCat` is Hausdorff locally compact. -/
@[stacks 09WZ "Hausdorff locally compact pullbacks"]
theorem pullback {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hX : LCCat.property X) (hY : LCCat.property Y)
    [T2Space Z] : LCCat.property (Limits.pullback f g) := by
  letI := hX.1
  letI := hX.2
  letI := hY.1
  letI := hY.2
  have hclosed : IsClosed {p : X × Y | f p.1 = g p.2} :=
    isClosed_eq (f.hom.continuous.comp continuous_fst) (g.hom.continuous.comp continuous_snd)
  let e := TopCat.homeoOfIso (TopCat.pullbackIsoProdSubtype f g)
  refine ⟨e.symm.t2Space, e.locallyCompactSpace_iff.mpr ?_⟩
  change LocallyCompactSpace {p : X × Y // f p.1 = g p.2}
  exact hclosed.locallyCompactSpace

/-- The Hausdorff locally compact object property is closed under pullback-shaped limits. -/
@[stacks 09WZ "Hausdorff locally compact spaces are closed under pullbacks", instance]
instance isClosedUnderPullbacks :
    ObjectProperty.IsClosedUnderLimitsOfShape
      LCCat.property WalkingCospan := by
  refine ObjectProperty.IsClosedUnderLimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  letI := (hF WalkingCospan.one).1
  exact LCCat.property.prop_of_iso (HasLimit.isoOfNatIso (diagramIsoCospan F)).symm
    (pullback (F.map WalkingCospan.Hom.inl) (F.map WalkingCospan.Hom.inr)
      (hF _) (hF _))

end LCCat.property

namespace LCCat

/-- Lemma 21.31.1 (1): `LCCat` has pullbacks. -/
@[stacks 09WZ "(1)"]
instance instHasPullbacks : HasPullbacks LCCat.{u} :=
  hasLimitsOfShape_of_closedUnderLimits WalkingCospan property

/-- Lemma 21.31.1 (2): `LCCat` has a terminal object. -/
@[stacks 09WZ "(2)"]
instance instHasTerminal : HasTerminal LCCat.{u} := by
  letI (Y : LCCat.{u}) : Unique (Y ⟶ of PUnit.{u + 1}) :=
    { default := ObjectProperty.homMk (TopCat.ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩)
      uniq := fun f ↦ by ext x }
  exact hasTerminal_of_unique (of PUnit.{u + 1})

/-- Lemma 21.31.1 (3): `LCCat` has all finite limits. -/
@[stacks 09WZ "(3)"]
instance instHasFiniteLimits : HasFiniteLimits LCCat.{u} :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- Lemma 21.31.1 (4): a pullback in `LCCat` of two compact source spaces is compact. -/
@[stacks 09WZ "(4)"]
instance compactSpace_pullback {X Y Z : LCCat.{u}} [CompactSpace X.obj]
    [CompactSpace Y.obj] (f : X ⟶ Z) (g : Y ⟶ Z) :
    CompactSpace (Limits.pullback f g).obj := sorry

end LCCat
