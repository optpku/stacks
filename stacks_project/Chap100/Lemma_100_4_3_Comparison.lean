module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Pullback

/-!
# A 2-commutative square of algebraic stacks

The concrete square presentation remains available alongside the shared point comparison API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Bicategory

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Points

section

variable {S : Scheme.{u}} {P X Z Y : GroupoidsOver S}
variable [AlgebraicStack P] [AlgebraicStack X] [AlgebraicStack Z] [AlgebraicStack Y]
variable {fst : P ⟶ X} {snd : P ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}

/-- The readable 2-commutative square with apex `P` associated to a 2-fibre product of algebraic
stacks. -/
def cone (iso : fst ≫ f ≅ snd ≫ g) : PseudoPullbackCone f g :=
  ⟨P, fst, snd, iso⟩

end

end AlgebraicGeometry.AlgebraicStack.Points
