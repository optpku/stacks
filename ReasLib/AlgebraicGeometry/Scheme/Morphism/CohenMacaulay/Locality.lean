/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.Syntomic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyNoetherianFibers
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison

/-!
# Locality of locally Noetherian Cohen--Macaulay morphisms

This file records locality properties of morphisms whose fibres are locally
Noetherian and which are Cohen--Macaulay.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.LocallyNoetherianCohenMacaulay

/-- Having locally Noetherian fibres and being Cohen--Macaulay is local at the
target for the fppf precoverage. -/
instance isLocalAtTargetFppf :
    MorphismProperty.IsLocalAtTarget
      ((AlgebraicGeometry.LocallyNoetherianFibers ⊓
          (@AlgebraicGeometry.CohenMacaulay :
            MorphismProperty AlgebraicGeometry.Scheme.{u})) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage := sorry

/-- Having locally Noetherian fibres and being Cohen--Macaulay is local at the
source for the syntomic precoverage. -/
instance isLocalAtSourceSyntomic :
    MorphismProperty.IsLocalAtSource
      ((AlgebraicGeometry.LocallyNoetherianFibers ⊓
          (@AlgebraicGeometry.CohenMacaulay :
            MorphismProperty AlgebraicGeometry.Scheme.{u})) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSyntomicPrecoverage := sorry

end AlgebraicGeometry.LocallyNoetherianCohenMacaulay
