/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic
public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfType

/-- Local complete-intersection morphisms of schemes are local on the source for the
syntomic precoverage. -/
instance isLocalCompleteIntersection_isLocalAtSourceSyntomic :
    MorphismProperty.IsLocalAtSource
      ((fun _ _ f ↦ AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSyntomicPrecoverage := sorry

end AlgebraicGeometry.LocallyOfType
