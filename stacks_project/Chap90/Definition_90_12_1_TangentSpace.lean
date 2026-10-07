module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap90.Definition_90_6_2_Predeformation
public import stacks_project.Chap90.Definition_90_12_1_DualNumber

/-!
# Tangent space of a predeformation category

The tangent space `T F` of a predeformation category `p : F ⥤ ArtinianLocalAlgCat Λ k` is the
type of isomorphism classes of objects in the fibre of `p` over the dual numbers.
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
    (x : p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k)) : tangentSpace p :=
  Quotient.mk'' x

/-- Two dual-number fibre objects determine the same tangent vector if and only if they are
isomorphic in the fibre. -/
theorem tangentSpace.mk_eq_mk [IsPredeformationCategory p]
    (x y : p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k)) :
    tangentSpace.mk p x = tangentSpace.mk p y ↔ Nonempty (x ≅ y) := sorry

end CategoryTheory.Functor
