module

public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace
import StacksCheckRecall

/-!
# Tangent space of a predeformation category

The tangent space of a predeformation category is the set of isomorphism classes of objects
in the fibre over the dual numbers.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsPredeformationCategory p]

/- Definition 90.12.1: the tangent space `T F` of a predeformation category `F` is the set of
isomorphism classes of objects in the fibre category `F(DualNumber k)`. -/
@[stacks 06IG]
#check (CategoryTheory.Functor.tangentSpace p : Type v)
