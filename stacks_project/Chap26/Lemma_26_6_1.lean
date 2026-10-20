/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.GlobalSections.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.6.1: the point map of a morphism to an affine scheme is induced
by its contravariant map on global sections. -/
@[stacks 01HY] #check LocallyRingedSpace.Hom.apply_eq_isoSpec_inv
#check LocallyRingedSpace.Hom.isoSpec_apply
