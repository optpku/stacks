module

public import Mathlib.AlgebraicGeometry.Scheme
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

/- 27.16.4.1: `F` is an arbitrary contravariant set-valued functor on schemes. -/
@[stacks 01NX] #check (CategoryTheory.Functor AlgebraicGeometry.Scheme.{u}ᵒᵖ (Type u) : Type (u + 1))

end
