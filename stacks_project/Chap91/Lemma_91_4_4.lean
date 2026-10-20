/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.Obstruction
import StacksCheckRecall

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open scoped AlgebraicGeometry

universe u

/- Lemma 91.4.4: A prescribed infinitesimal comparison admits an extension exactly when
its degree-two existence obstruction vanishes. The equivalence
`infinitesimalComparisonEquiv` identifies these comparisons with all intrinsic maps
`idealModule i ⊗ F ⟶ K`. -/
@[stacks 08L8] #check
  (AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.existenceObstruction_eq_zero_iff :
    ∀ {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i]
      (F K : X.Modules) [HasExt.{u} X.Modules]
      (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K),
      InfinitesimalExtension.existenceObstruction i F K c = 0 ↔
        Nonempty (InfinitesimalExtension i F K c))
