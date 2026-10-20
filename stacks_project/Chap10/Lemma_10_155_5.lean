/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.IndEtale.Henselian.ResiduePoint
import StacksCheckRecall

/-!
# Etale lifting to a henselization

@stack 04GR

The reusable owner works for an arbitrary ind-etale algebra and Henselian local target.  When the
canonical source residue map is bijective, the inverse image of the closed point alone
characterizes the unique lift.  Etale algebras and henselizations give the source specialization.
-/

@[expose] public section

@[stacks 04GR "unique lift characterized by its inverse-image prime"]
#check @RingHom.IndEtale.ResiduePoint.existsUnique_lift_ofIdeal_comap_ofBijective
