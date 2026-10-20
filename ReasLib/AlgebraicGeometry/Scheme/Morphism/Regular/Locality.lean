/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Regular.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyNoetherianFibers
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Regular.Smooth

/-!
# Locality of locally Noetherian regular morphisms of schemes

This file records locality properties of regular morphisms with locally Noetherian fibres.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.LocallyNoetherianRegular

/-- Having locally Noetherian fibres and being regular is local on the target for the fppf
precoverage. -/
instance isLocalAtTargetFppf :
    MorphismProperty.IsLocalAtTarget
      ((AlgebraicGeometry.LocallyNoetherianFibers ⊓ @AlgebraicGeometry.Regular) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage := sorry

/-- Having locally Noetherian fibres and being regular is local on the source for the smooth
precoverage. -/
instance isLocalAtSourceSmooth :
    MorphismProperty.IsLocalAtSource
      ((AlgebraicGeometry.LocallyNoetherianFibers ⊓ @AlgebraicGeometry.Regular) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage := sorry

end AlgebraicGeometry.LocallyNoetherianRegular
