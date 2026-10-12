/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Closure

@[expose] public section

/-!
# Residue fields of locally finite-type morphisms

This leaf records finite-generation properties of residue-field extensions induced by locally
finite-type morphisms, including the closed-point algebraicity consequence for schemes over a
field.
-/

open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyOfFiniteType

/-- At every point of a locally finite-type scheme morphism, the induced residue-field extension
is essentially of finite type. -/
theorem residueField_essFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    Algebra.EssFiniteType (S.residueField (f x)) (X.residueField x) := sorry

/-- For a scheme locally of finite type over a field, the residue field at every closed point is
algebraic over the base field. -/
@[stacks 0478]
theorem residueField_isAlgebraic_of_closedPoint
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (x : X) (hx : x ∈ closedPoints X) :
    Scheme.Hom.ResidueField.IsAlgebraicOverSpec f x := sorry

end AlgebraicGeometry.LocallyOfFiniteType
