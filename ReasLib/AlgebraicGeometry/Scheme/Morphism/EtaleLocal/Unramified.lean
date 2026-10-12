/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Unramified
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Locality

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Unramified

/-- Unramifiedness of scheme morphisms is étale local on the source and target. -/
instance isEtaleLocalAtSourceAndTarget :
    AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
      (@AlgebraicGeometry.Unramified : MorphismProperty AlgebraicGeometry.Scheme.{u}) := sorry

end AlgebraicGeometry.Unramified

namespace AlgebraicGeometry.GUnramified

/-- G-unramifiedness of scheme morphisms is étale local on the source and target. -/
instance isEtaleLocalAtSourceAndTarget :
    AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
      (@AlgebraicGeometry.GUnramified : MorphismProperty AlgebraicGeometry.Scheme.{u}) := sorry

end AlgebraicGeometry.GUnramified
