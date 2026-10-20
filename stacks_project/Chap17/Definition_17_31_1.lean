/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent
import StacksCheckRecall

@[expose] public section

open SheafOfModules.RingedSite

/- Definition 17.31.1 (08TJ): for sheaves of commutative rings on a topological space, the naive
cotangent complex is the canonical two-term conormal complex.  The ringed-site owner is already
more general and specializes directly to the opens site. -/
@[stacks 08TJ]
#check @NaiveCotangent.obj

#check @NaiveCotangent.X_negOne
#check @NaiveCotangent.X_zero
#check @NaiveCotangent.d_negOne_zero
#check @NaiveCotangent.augmentation
#check @NaiveCotangent.Augmentation.homologyMapZeroInv
#check @NaiveCotangent.Augmentation.homologyMapZeroIso
#check @NaiveCotangent.homologyZeroIso
#check @NaiveCotangent.homologyZeroMap
#check @NaiveCotangent.homologyZeroInv
#check @NaiveCotangent.homologyZeroMap_comp_inv
#check @NaiveCotangent.homologyZeroInv_comp_map
#check @NaiveCotangent.homologyZeroIso_hom
#check @NaiveCotangent.homologyZeroIso_inv
