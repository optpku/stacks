module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Category
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.Small

/-!
# The Picard stack of a morphism of algebraic spaces

The Picard projection is a stack in groupoids for the fppf topology, and its
fibers are essentially small.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The Picard projection of a morphism of algebraic spaces over `S` is a stack
in groupoids for the fppf topology on schemes over `S`. -/
instance isStackInGroupoids (f : X ⟶ B) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (p f) := sorry

/-- Every fiber of the Picard projection over a scheme over `S` is essentially
`u`-small. -/
instance fibers_essentiallySmall (f : X ⟶ B) (U : Over S) :
    ObjectProperty.EssentiallySmall.{u}
      (⊤ : ObjectProperty ((p f).Fiber U)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
