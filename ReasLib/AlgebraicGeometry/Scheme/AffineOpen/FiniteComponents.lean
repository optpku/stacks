/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent

/-!
# Affine neighborhoods from irreducible components

A finite subset of a scheme lies in one affine open when it does so on every irreducible
component and the scheme has only finitely many irreducible components.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A finite subset of a scheme with finitely many irreducible components is contained in a
single affine open if its inverse image in every reduced irreducible-component subscheme is
contained in an affine open. -/
theorem exists_affineOpen_containing_finiteSet_of_irreducibleComponents
    {X : Scheme.{u}} [Finite (irreducibleComponents X)] (T : Set X) (hT : T.Finite)
    (hcomp : ∀ Z : irreducibleComponents X,
      let Y := X.irreducibleComponentSubscheme Z
      let i : Y ⟶ X := X.irreducibleComponentSubschemeι Z
      ∃ U : Y.affineOpens, ∀ x : Y, i x ∈ T → x ∈ ((U : Y.Opens) : Set Y)) :
    ∃ U : X.affineOpens, T ⊆ ((U : X.Opens) : Set X) := sorry

end AlgebraicGeometry.Scheme
