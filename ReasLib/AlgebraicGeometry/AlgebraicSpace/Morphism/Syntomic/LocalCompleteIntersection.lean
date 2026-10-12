/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.LocalCompleteIntersection

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Syntomic

/-- A morphism of algebraic spaces is syntomic if and only if it is flat and a
local complete intersection. -/
theorem iff_flat_and_isLocalCompleteIntersection {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Syntomic f ↔ Flat f ∧ IsLocalCompleteIntersection f := sorry

/-- A syntomic morphism of algebraic spaces is a local complete intersection. -/
instance isLocalCompleteIntersection {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Syntomic f] : IsLocalCompleteIntersection f := sorry

end AlgebraicGeometry.AlgebraicSpace.Syntomic

namespace AlgebraicGeometry.AlgebraicSpace

/-- A flat local complete intersection morphism of algebraic spaces is
syntomic. -/
instance syntomic_of_flat_of_isLocalCompleteIntersection {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f]
    [IsLocalCompleteIntersection f] : Syntomic f := sorry

end AlgebraicGeometry.AlgebraicSpace
