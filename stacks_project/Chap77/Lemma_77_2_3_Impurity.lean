/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Impurity

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsImpurity :
  {S : Scheme.{u}} → {X Y : AlgebraicSpace S} →
    (f : X ⟶ Y) → (F : X.Modules) → (y : Points Y) → (T : SchemeOver Y) →
    (t' t : T.left.left) → (ξ : Points (Limits.pullback f T.hom)) → Prop)
