/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.RingTheory.Coherent.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v

namespace ModuleCat

/-- Finitely presented modules over a coherent commutative ring form a category with finite
limits. -/
instance instHasFiniteLimits_isFinitePresentation_of_isCoherentRing
    {A : Type u} [CommRing A] [IsCoherentRing A] :
    HasFiniteLimits (isFinitePresentation.{u, max u v} A).FullSubcategory := sorry

end ModuleCat
