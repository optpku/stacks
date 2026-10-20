/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheaf
import StacksCheckRecall

open CategoryTheory

universe u v

/- Lemma 35.13.7: every representable functor on the category of schemes satisfies
the sheaf condition for the fpqc topology. -/
@[stacks 023Q] #check
  (AlgebraicGeometry.isSheaf_fpqcTopology_of_isRepresentable :
    ∀ (P : (AlgebraicGeometry.Scheme.{u})ᵒᵖ ⥤ Type v) [P.IsRepresentable],
      CategoryTheory.Presieve.IsSheaf AlgebraicGeometry.Scheme.fpqcTopology P)
