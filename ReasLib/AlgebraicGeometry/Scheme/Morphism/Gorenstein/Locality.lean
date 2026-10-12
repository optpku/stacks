/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein.Syntomic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyNoetherianFibers
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison

/-!
# Locality of locally Noetherian Gorenstein morphisms

This file records locality properties of morphisms whose fibres are locally
Noetherian and which are Gorenstein.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.LocallyNoetherianGorenstein

/-- Having locally Noetherian fibres and being Gorenstein is local at the
target for the fppf precoverage. -/
instance isLocalAtTargetFppf :
    MorphismProperty.IsLocalAtTarget
      ((AlgebraicGeometry.LocallyNoetherianFibers ⊓
          (@AlgebraicGeometry.Gorenstein :
            MorphismProperty AlgebraicGeometry.Scheme.{u})) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage := sorry

/-- Having locally Noetherian fibres and being Gorenstein is local at the
source for the syntomic precoverage. -/
instance isLocalAtSourceSyntomic :
    MorphismProperty.IsLocalAtSource
      ((AlgebraicGeometry.LocallyNoetherianFibers ⊓
          (@AlgebraicGeometry.Gorenstein :
            MorphismProperty AlgebraicGeometry.Scheme.{u})) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSyntomicPrecoverage := sorry

end AlgebraicGeometry.LocallyNoetherianGorenstein
