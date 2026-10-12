/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber

/-!
# Tangent space of a predeformation category

The tangent space of a predeformation category is the type of isomorphism classes of objects
in its fibre over the dual numbers.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

namespace CategoryTheory.Functor

/-- The tangent space of a predeformation category is the type of isomorphism classes of
objects in the fibre over `ArtinianLocalAlgCat.dualNumber Λ k`. -/
def tangentSpace [IsPredeformationCategory p] : Type v :=
  isomorphismClasses.obj (Cat.of (p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k)))

/-- The tangent space is definitionally the type of isomorphism classes of the dual-number
fibre. -/
theorem tangentSpace_def [IsPredeformationCategory p] :
    tangentSpace p =
      isomorphismClasses.obj (Cat.of (p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k))) := sorry

/-- The isomorphism class of an object of the fibre over the dual numbers. -/
def tangentSpace.mk [IsPredeformationCategory p]
    (fiberObject : p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k)) : tangentSpace p :=
  Quotient.mk'' fiberObject

/-- Two dual-number fibre objects determine the same tangent vector if and only if they are
isomorphic in the fibre. -/
theorem tangentSpace.mk_eq_mk [IsPredeformationCategory p]
    (fiberObject otherObject : p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k)) :
    tangentSpace.mk p fiberObject = tangentSpace.mk p otherObject ↔
      Nonempty (fiberObject ≅ otherObject) := sorry

end CategoryTheory.Functor
