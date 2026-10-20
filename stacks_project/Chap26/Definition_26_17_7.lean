/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Pullback

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable (I : Y.IdealSheafData)

/- Definition 26.17.7: the inverse image of a closed subscheme is defined
by pulling back its ideal sheaf and is canonically the relevant fibre
product. -/
@[stacks 01JV] #check I.comap f
@[stacks 01JV] #check I.comapIso f
#check I.comapIso_hom_fst f

/- The fixed-support layer records the inverse image of the prescribed closed subset while
retaining the same ideal-sheaf and pullback owners. -/
variable {Z : Closeds Y} (T : Scheme.ClosedSubschemeStructure Z)

#check Scheme.ClosedSubschemeStructure.ofIdeal I
#check T.comap f
#check T.comapIso f
#check T.comapIso_hom_fst f
#check T.comapIso_inv_ι f
