/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Separation.Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.4.10 (1): if `g ∘ f` is separated then so is `f`. -/
@[stacks 03KR] #check
  (AlgebraicGeometry.AlgebraicSpace.Separated.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [Separated (f ≫ g)], Separated f)

/- Lemma 67.4.10 (2): if `g ∘ f` is locally separated then so is `f`. -/
@[stacks 03KR] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallySeparated.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [LocallySeparated (f ≫ g)], LocallySeparated f)

/- Lemma 67.4.10 (3): if `g ∘ f` is quasi-separated then so is `f`. -/
@[stacks 03KR] #check
  (AlgebraicGeometry.AlgebraicSpace.QuasiSeparated.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [QuasiSeparated (f ≫ g)], QuasiSeparated f)
