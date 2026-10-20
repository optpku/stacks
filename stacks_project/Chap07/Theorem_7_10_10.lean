/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.TypeSheafification
public import StacksCheckRecall.CommandCrossRef

/-!
# Theorem 7.10.10

The reusable Type-valued plus-construction API is owned by ReasLib. This
source file records the textbook clauses as labelled recalls.
-/

@[expose] public section

open CategoryTheory Opposite
open GrothendieckTopology Plus

/- Theorem 7.10.10 (00WB) (1): the plus construction `J.plusObj F` is separated. -/
@[stacks 00WB "(1)"] #check @CategoryTheory.GrothendieckTopology.plusObj_isSeparated

/- Theorem 7.10.10 (00WB) (2): for a separated presheaf, the plus construction is a sheaf and
the plus unit is sectionwise injective; the companion monomorphism formulation is also reusable. -/
@[stacks 00WB "(2) sheaf"] #check @CategoryTheory.GrothendieckTopology.plusObj_isSheaf_of_isSeparated

@[stacks 00WB "(2) injective"] #check @CategoryTheory.GrothendieckTopology.toPlus_injective_of_isSeparated

@[stacks 00WB "(2) mono"] #check @CategoryTheory.GrothendieckTopology.toPlus_mono_of_isSeparated

#check @CategoryTheory.Presheaf.mono_iff_injective

/- Theorem 7.10.10 (00WB) (3): the plus unit of an already sheaf presheaf is invertible. -/
@[stacks 00WB "(3)"] #check @GrothendieckTopology.isIso_toPlus_of_isSheaf

/- Theorem 7.10.10 (00WB) (4): the iterated plus construction is a sheaf. -/
@[stacks 00WB "(4)"] #check @GrothendieckTopology.Plus.isSheaf_plus_plus
