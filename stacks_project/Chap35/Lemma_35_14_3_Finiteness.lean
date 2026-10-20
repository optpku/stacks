/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Descent

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.LocallyOfFinitePresentation.hasOfPrecompFppf :
    MorphismProperty.HasOfPrecompProperty
      (@AlgebraicGeometry.LocallyOfFinitePresentation :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      ((@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓
        @AlgebraicGeometry.LocallyOfFinitePresentation) :
        MorphismProperty AlgebraicGeometry.Scheme.{u}))

#check (AlgebraicGeometry.LocallyOfFiniteType.hasOfPrecompFppf :
    MorphismProperty.HasOfPrecompProperty
      (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      ((@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓
        @AlgebraicGeometry.LocallyOfFinitePresentation) :
        MorphismProperty AlgebraicGeometry.Scheme.{u}))
