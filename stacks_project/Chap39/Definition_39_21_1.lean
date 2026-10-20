/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.GroupoidScheme.Cartesian
import StacksCheckRecall

universe u

/- Definition 39.21.1 (1): A morphism of groupoid schemes over `S` is cartesian when the
square formed by its arrow map, object map, and the two source maps is a pullback in `Scheme`. -/
@[stacks 0APD] #check (AlgebraicGeometry.GroupoidScheme.Hom.IsCartesian :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {G G' : AlgebraicGeometry.GroupoidScheme S} →
      AlgebraicGeometry.GroupoidScheme.Hom G G' → Prop)

/- Definition 39.21.1 (2): The groupoid schemes cartesian over a fixed groupoid scheme `G`,
with morphisms compatible with their structure morphisms to `G`. -/
@[stacks 0APD] #check (AlgebraicGeometry.GroupoidScheme.CartesianOver :
  {S : AlgebraicGeometry.Scheme.{u}} →
    AlgebraicGeometry.GroupoidScheme S → CategoryTheory.Cat)
