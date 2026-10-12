/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.AffineDescent

/-!
# Target locality of flatness

This file records target locality of flatness for morphisms of schemes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Flat

/-- Flatness of scheme morphisms is local on the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Flat : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.Flat
