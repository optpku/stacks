/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.Pushout

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

/-!
# Functoriality of 08L4 extensions along morphisms of first-order thickenings
-/

/- Remark 91.4.7 -/
@[stacks 08LC] #check (AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.pushout :
  ∀ {X X1 X2 : AlgebraicGeometry.RingedSpace} {i1 : X ⟶ X1}
    [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening i1] {h : X1 ⟶ X2}
    [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
      (CategoryTheory.CategoryStruct.comp i1 h)]
    {F K1 K2 : X.Modules},
    (c1 : AlgebraicGeometry.RingedSpace.Hom.kernelIdealSheaf i1 ⊗
        (i1 _*).obj F ⟶ (i1 _*).obj K1) →
      {c2 : AlgebraicGeometry.RingedSpace.Hom.kernelIdealSheaf
          (CategoryTheory.CategoryStruct.comp i1 h) ⊗
          ((CategoryTheory.CategoryStruct.comp i1 h) _*).obj F ⟶
            ((CategoryTheory.CategoryStruct.comp i1 h) _*).obj K2} →
        (κ : K2 ⟶ K1) →
          AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.infinitesimalMapCommSq
            c1 c2 κ →
            AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension
              (CategoryTheory.CategoryStruct.comp i1 h) F K2 c2 →
              AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension i1 F K1 c1)
