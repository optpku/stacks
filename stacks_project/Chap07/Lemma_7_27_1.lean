/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Localization.LowerShriek.Subcanonical
public import StacksCheckRecall.CommandCrossRef

@[expose] public section

/-!
# Lemma 7.27.1

The subcanonical localization formula is owned by the ReasLib lower-shriek
subcanonical leaf; this file records the source-facing recall.
-/

/- Lemma 7.27.1 (03HT): if `J` is subcanonical and `G` is a sheaf on `C / U`,
then the left Kan extension of `G` is a sheaf and the underlying presheaf of
localization lower shriek evaluates at `V` as `Σ φ : V ⟶ U, G(Over.mk φ)`. -/
@[stacks 03HT] #check @CategoryTheory.GrothendieckTopology.Localization.LowerShriek.Subcanonical.isSheaf_lan

@[stacks 03HT] #check @CategoryTheory.GrothendieckTopology.Localization.LowerShriek.Subcanonical.underlyingIsoLan

@[stacks 03HT] #check @CategoryTheory.GrothendieckTopology.Localization.LowerShriek.Subcanonical.objIsoSigma
