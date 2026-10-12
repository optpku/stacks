/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Dominant.GenericPoint

/-!
# Dominance of birational morphisms

This module records the relation between birational and dominant scheme morphisms.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A birational morphism between schemes with finitely many irreducible components is
dominant. -/
instance instIsDominantOfIsBirational
    {X Y : Scheme.{u}} [Finite (irreducibleComponents X)] [Finite (irreducibleComponents Y)]
    (f : X ⟶ Y) [IsBirational f] : IsDominant f := sorry

end AlgebraicGeometry
