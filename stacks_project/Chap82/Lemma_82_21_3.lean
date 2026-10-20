/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow.Commutativity
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom

universe u

/- Lemma 82.21.3 -/
@[stacks 0EQZ] #check (AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow.cap_comm :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (L N : X.Modules) [isInvertibleObject L] [isInvertibleObject N]
      (k : ℤ) (α : Hom.chowGroup f δ (k + 1 + 1)),
      AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow.cap
          f δ L k
          (AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow.cap
            f δ N (k + 1) α) =
        AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow.cap
          f δ N k
          (AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow.cap
            f δ L (k + 1) α))
