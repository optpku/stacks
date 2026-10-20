/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.FilteredColimits.Ordinal
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.10

The cardinally generated-cover and ordinal-colimit APIs are owned by ReasLib;
this Chapter 7 entry is a source-facing recall block.
-/

@[expose] public section

/- Lemma 7.17.10 (0GS0): for an ordinal-indexed system of sheaves on a site,
the canonical map from the colimit of the sections over `U` to the sections of
the colimit is bijective when the cofinality of the ordinal dominates the
index cardinalities of chosen covering families.  The formal API represents
those chosen families explicitly and provides a bridge to the equivalent
raw-presieve cardinal formulation. -/
@[stacks 0GS0] #check @CategoryTheory.Presieve.GeneratingFamily

@[stacks 0GS0] #check @CategoryTheory.Precoverage.hasCardinalLTCoveringPresieves

@[stacks 0GS0] #check @CategoryTheory.Precoverage.hasCardinalLTGeneratingFamilies_iff

@[stacks 0GS0] #check @CategoryTheory.Sites.FilteredColimitSections.isIso_of_ordinal

@[stacks 0GS0] #check @CategoryTheory.Precoverage.FilteredColimitSections.isIso_of_ordinal

@[stacks 0GS0] #check @CategoryTheory.Precoverage.FilteredColimitSections.bijective_of_ordinal
