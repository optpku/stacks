/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat.Point
import StacksCheckRecall

/-!
# Definition 17.20.1

Flatness of a ringed-space morphism is the stalkwise flatness of its local-ring maps.
-/

@[expose] public section

/- Definition 17.20.1 (1): flatness at one source point. -/
@[stacks 02N3 "(1)"]
#check @RingedSpace.Hom.FlatAt

/- Definition 17.20.1 (2): flatness at every source point. -/
@[stacks 02N3 "(2)"]
#check @RingedSpace.Hom.IsFlat

/- Point inclusions are a reusable special case of flat ringed-space morphisms. -/
#check @AlgebraicGeometry.pointInclusion_isFlat
