module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap84.Lemma_84_4_4_Comparison

/-!
# Lemma 84.4.4

Proper base change for sheaves of sets on the small étale site of an algebraic
space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))

/-- Lemma 84.4.4: if `f : X ⟶ Y` is a proper morphism of algebraic spaces over a
scheme `S` and `g : Y' ⟶ Y` is any morphism, with cartesian projections
`f' : X' ⟶ Y'` and `g' : X' ⟶ X`, then for any sheaf of sets `F` on `X_étale`
the comparison `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is an isomorphism. -/
@[stacks 0DG0]
theorem proper_baseChange_isIso [Proper f] :
    IsIso (smallEtaleBaseChangeHom f g f' g' h_cart F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
