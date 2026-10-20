module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import StacksCheckRecall

/-!
@stack 018G

# Definition 14.20.1 compatibility facade

An augmentation with fixed source and target is a morphism to a constant simplicial object.
Mathlib additionally packages the varying source, target, and augmentation in
`SimplicialObject.Augmented`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SimplicialObject

universe u v

variable {C : Type u} [Category.{v} C]
variable (U : SimplicialObject C) (X : C)

/- Definition 14.20.1: an augmentation of `U` towards `X` is a morphism from `U` to the
constant simplicial object on `X`. -/
@[stacks 018G]
#check (U ⟶ (const C).obj X)

/- The bundled owner is used when the source and augmentation target vary together. -/
#check (SimplicialObject.Augmented C)
#check SimplicialObject.Augmented.drop
#check SimplicialObject.Augmented.point
