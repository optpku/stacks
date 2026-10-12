/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Additive

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BivariantClass

/-- Compatibility name for the canonical pointwise-zero bivariant class.
Both the vanishing and additive source interfaces use this single owner. -/
noncomputable abbrev zeroClass
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) : BivariantClass delta f p :=
  pointwiseZero delta f p

end AlgebraicGeometry.BivariantClass
