/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.LocalAtSource
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Etale

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Etale

/-- Étaleness of scheme morphisms is étale local on the source and target. -/
instance isEtaleLocalAtSourceAndTarget :
    AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
      (@AlgebraicGeometry.Etale : MorphismProperty AlgebraicGeometry.Scheme.{u}) := sorry

end AlgebraicGeometry.Etale
