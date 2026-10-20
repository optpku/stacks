/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.SesFlat
public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.Strict

/-!
# Short exact sequences of flat first-order thickenings

The canonical declarations for this diagram are owned by the reusable
first-order-thickening and thickening-morphism modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

#check @AlgebraicGeometry.RingedSpace.Thickening.Hom.IsStrict
#check @AlgebraicGeometry.RingedSpace.Thickening.Hom.isStrict_iff
#check @AlgebraicGeometry.RingedSpace.Thickening.Hom.isStrict_iff_sourceIdealMap
#check @AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.SesFlatThickenings
#check @AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.SesFlatThickenings.of
#check @AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.SesFlatThickenings.spec
#check @AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.SesFlatThickenings.restricts
#check @AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.SesFlatThickenings.thickenedSq
#check @AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.SesFlatThickenings.thickeningHom1
#check @AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.SesFlatThickenings.thickeningHom2
#check @AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.SesFlatThickenings.thickeningHom3
#check @AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.SesFlatThickenings.moduleRestrict
#check @AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.SesFlatThickenings.canonicalSplitting
#check @AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.SesFlatThickenings.canonicalSplitting_leftInv
#check @AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.SesFlatThickenings.top_isShortExact
