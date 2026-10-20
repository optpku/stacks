/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.KFlat.Stalk
import StacksCheckRecall

@[expose] public section

/-!
# Stalkwise K-flatness

The stalk-complex functor is owned by `GrothendieckTopology.Point`; the K-flatness statements
are reusable properties of complexes of modules on a commutative ringed site.
-/

/- Lemma 21.18.6 (0DEN) (1): K-flatness passes to every module-valued stalk complex. -/
@[stacks 0DEN "(1)"]
#check @SheafOfModules.RingedSite.CochainComplex.IsKFlat.stalk

/- Lemma 21.18.6 (0DEN) (2): on a site with enough points, K-flatness is detected on all
module-valued stalk complexes. -/
@[stacks 0DEN "(2)"]
#check @SheafOfModules.RingedSite.CochainComplex.isKFlat_iff_forall_stalk_of_hasEnoughPoints

#check @CategoryTheory.GrothendieckTopology.Point.moduleStalkComplex
#check @CategoryTheory.GrothendieckTopology.Point.moduleStalkComplex.obj_X
#check @SheafOfModules.RingedSite.CochainComplex.isKFlat_iff_forall_stalk_of_isConservativeFamily
