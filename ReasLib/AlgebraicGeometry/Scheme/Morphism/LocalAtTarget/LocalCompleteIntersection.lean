/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Finiteness
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.RegularImmersion

/-!
# Target locality of local complete-intersection morphisms

This file records target locality of local complete-intersection morphisms of schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfType

/-- Local complete-intersection morphisms of schemes are local on the target for the
fpqc precoverage. -/
instance isLocalCompleteIntersection_isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      ((fun _ _ f ↦ AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.LocallyOfType
