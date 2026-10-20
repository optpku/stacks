/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.NormalCrossings.EtaleLocal

universe u

#check (@AlgebraicGeometry.IsNormalCrossingsDivisor :
  ∀ {X : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.IsLocallyNoetherian X →
    X.IdealSheafData → Prop)
