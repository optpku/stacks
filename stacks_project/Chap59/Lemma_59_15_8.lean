/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/- Lemma 59.15.8: Any representable presheaf on schemes over S satisfies the fpqc sheaf condition. -/
@[stacks 03O3] #check (AlgebraicGeometry.isSheaf_fpqcTopology_over_of_isRepresentable :
    ∀ (S : Scheme.{u}) (P : (CategoryTheory.Over S)ᵒᵖ ⥤ Type v), [P.IsRepresentable] →
      CategoryTheory.Presieve.IsSheaf (Scheme.fpqcTopology.over S) P)

end AlgebraicGeometry
