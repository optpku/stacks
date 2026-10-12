/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.LocalAtSource

@[expose] public section

universe u

/- Syntomicity of scheme morphisms is local on the source for the syntomic precoverage. -/
#check
  (AlgebraicGeometry.Syntomic.isLocalAtSourceSyntomic :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.Syntomic :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSyntomicPrecoverage)
