/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pro.Sequential.Distinguished.ProZero
import StacksCheckRecall

@[expose] public section

/- Lemma 13.42.4: the first maps in a sequential system of distinguished triangles are a
pro-isomorphism when the third vertex system is pro-zero. -/
@[stacks 0G3C] #check @CategoryTheory.Pro.Sequential.Distinguished.ProZero.toHom_isIso

#check @CategoryTheory.Pro.HasValue
#check @CategoryTheory.Pro.SequentialHom.toHom_map_ofNatTrans
#check @CategoryTheory.Pro.Sequential.Distinguished.ProZero.quotientToHom_isIso
#check @CategoryTheory.Pro.Sequential.Distinguished.ProZero.hasRepresentativeInverse
#check @CategoryTheory.Pro.SequentialHom.isIso_toHom_iff_hasRepresentativeInverse
