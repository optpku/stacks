module

public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap76.Lemma_76_9_2_Thickening

/-!
# Thickenings of schemes as algebraic spaces

If a thickening of algebraic spaces has source representable by a scheme, then
so is the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsScheme

/-- Lemma 76.9.5: Let `S` be a scheme. Let `i : X ⟶ X'` be a thickening of
algebraic spaces over `S`. If `X` is (representable by) a scheme, then so is
`X'`. -/
@[stacks 05ZR]
theorem of_thickening {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsThickening i] [IsScheme X] : IsScheme X' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsScheme
