/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ClosedOpen
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 59.70.8: if `i : Z ⟶ X` is a closed immersion and
`j = (closedImmersionComplement i).ι` is the open complement inclusion,
then for every abelian sheaf `F` on `X_étale` the canonical sequence
`0 ⟶ j_! (j⁻¹ F) ⟶ F ⟶ i_* (i⁻¹ F) ⟶ 0` is short exact. -/
@[stacks 095L] #check
  (AlgebraicGeometry.Scheme.Etale.closedOpenShortComplex_shortExact :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
      (AlgebraicGeometry.Scheme.Etale.closedOpenShortComplex i F).ShortExact)
