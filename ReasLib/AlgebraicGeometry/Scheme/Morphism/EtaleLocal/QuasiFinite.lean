/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Locality

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteType

/-- Local finite-type quasi-finiteness of scheme morphisms is étale local on the source and
target. -/
theorem locallyQuasiFiniteIsEtaleLocalAtSourceAndTarget :
    AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
      ((@AlgebraicGeometry.LocallyOfFiniteType ⊓ @AlgebraicGeometry.LocallyQuasiFinite) :
        MorphismProperty AlgebraicGeometry.Scheme.{u}) := sorry

end AlgebraicGeometry.Scheme.Hom.FiniteType
