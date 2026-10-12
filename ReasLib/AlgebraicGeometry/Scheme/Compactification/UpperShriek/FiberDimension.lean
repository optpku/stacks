/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.FiberDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.LocalDescription
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.ProjectionFormula
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.RingedSpace.ModuleDerived

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek

/-- If a degree of the cohomology stalk of the compactification model of upper shriek
is nontrivial, then that degree is at least the negative local dimension of the fibre. -/
theorem neg_fiberDimension_le_of_cohomologyStalk_nontrivial
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    (x : X.obj.left) (d : ℕ)
    (h_dimension : fiberDimensionAt f.hom.left x = (d : WithBot ℕ∞))
    (i : ℤ)
    (hi : Nontrivial (cohomologyStalk (dualizingObject f P A).obj i x)) :
    -(d : ℤ) ≤ i := sorry

end AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek
