/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.InverseImage.Acyclic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.37.4

This is the stronger total-acyclicity statement.  In addition to continuity and cocontinuity, it
retains the source hypothesis that the sheaf lower-shriek functor
`f.sheafPullback (Type z) J K : Sheaf J (Type z) ⥤ Sheaf K (Type z)` preserves pullbacks.  The
chosen lower-shriek owner also carries the necessary `IsRightAdjoint` existence instance.
-/

open CategoryTheory CategoryTheory.Limits

/- Lemma 21.37.4 (0D6Y): preservation of fibre products by sheaf lower shriek upgrades the
inverse image of an injective module to a totally acyclic sheaf. -/
@[stacks 0D6Y]
#check @RingedSite.Cocontinuous.moduleInverseImage.isTotallyAcyclic_of_injective

/- Mathlib's chosen sheaf lower-shriek functor for a continuous site functor. -/
#check @CategoryTheory.Functor.sheafPullback

/- The canonical predicate for total acyclicity of an abelian sheaf. -/
#check @CategoryTheory.Sheaf.IsTotallyAcyclic
