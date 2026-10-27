/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory

universe u

/- Lemma 82.26.4: In Situation 82.2.1 let `X / B` be good. Let `L` be an
invertible `𝒪_X`-module. Then the rule sending a good test map `g : Y ⟶ X`
to `c₁(g^* L) ∩ - : CH_k(Y) → CH_{k-1}(Y)` is a degree-1 identity bivariant
class. -/
@[stacks 0ERM] #check
  (AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern.degree :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (L : X.Modules) [isInvertibleObject L],
      OperationalChow δ f 1)

#check
  (AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern.degree_cap :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (L : X.Modules) [isInvertibleObject L]
      {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ),
      (OperationalFirstChern.degree f δ L).cap g k =
        @FirstChernChow.lower S B Y _ _ (g ≫ f) _ _ δ _
          ((Modules.pullback g).obj L) (Modules.isInvertibleObject_pullback g L) k)
