/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Regular
public import stacks_project.Chap71.Definition_71_10_3_MeromorphicSection

/-! Compatibility facade for regular meromorphic sections. -/

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.IsRegularMeromorphicSection :
    {S : AlgebraicGeometry.Scheme.{u}} → (X : AlgebraicGeometry.AlgebraicSpace S) →
      (F : X.Modules) → AlgebraicGeometry.AlgebraicSpace.meromorphicSections X F → Prop)
