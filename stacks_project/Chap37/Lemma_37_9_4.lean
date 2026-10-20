/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation.Presheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.Deformation

/- Lemma 37.9.4: compatible local lifts of a morphism between first-order thickenings,
with a prescribed conormal map, form a sheaf of sets on `X'`. -/
@[stacks 04FH]
#check
  (AlgebraicGeometry.Scheme.Hom.Deformation.presheaf_isSheaf :
    ∀ {S X X' Y Y' : Scheme.{u}} (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
      [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
      [IsFirstOrderThickening i] [IsFirstOrderThickening j]
      [i.IsOver S] [j.IsOver S] [a.IsOver S]
      (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
        Scheme.Hom.conormalSheaf i),
      TopCat.Presheaf.IsSheaf (presheaf S i j a A))

end AlgebraicGeometry.Scheme.Hom.Deformation
