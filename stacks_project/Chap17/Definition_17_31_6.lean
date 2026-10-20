/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Definition 17.31.6 (08TN): the naive cotangent complex `NL[f]` of a morphism of ringed spaces is the
opens-site specialization of the canonical ringed-site construction. -/
@[stacks 08TN]
#check @RingedSpace.naiveCotangent

#check @RingedSpace.inverseImageStructureSheafUnder
#check @RingedSpace.naiveCotangent_X_negOne
#check @RingedSpace.naiveCotangent_X_zero
#check @RingedSpace.naiveCotangent_d_negOne_zero
#check @RingedSpace.NaiveCotangent.augmentation
#check @RingedSpace.NaiveCotangent.Augmentation.homologyMapZeroInv
#check @RingedSpace.NaiveCotangent.Augmentation.homologyMapZeroIso
#check @RingedSpace.NaiveCotangent.homologyZeroIso
#check @RingedSpace.NaiveCotangent.homologyZeroMap
#check @RingedSpace.NaiveCotangent.homologyZeroInv
#check @RingedSpace.NaiveCotangent.homologyZeroMap_comp_inv
#check @RingedSpace.NaiveCotangent.homologyZeroInv_comp_map
#check @RingedSpace.NaiveCotangent.homologyZeroIso_hom
#check @RingedSpace.NaiveCotangent.homologyZeroIso_inv
