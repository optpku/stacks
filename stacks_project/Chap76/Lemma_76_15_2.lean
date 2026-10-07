module

public import stacks_project.Chap76.«76_15_0_1_Universal»
public import stacks_project.Chap76.Lemma_76_16_4_FormallyEtale

/-!
# Universal first-order thickenings over formally étale morphisms

A universal first-order thickening of `Z` over `Y` remains a universal
first-order thickening of `Z` over `X` after postcomposition with a
formally étale morphism `Y ⟶ X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder

/-- Lemma 76.15.2: Let `S` be a scheme. Let `Z ⟶ Y ⟶ X` be morphisms of
algebraic spaces over `S`. If `i : Z ⟶ Z'` is a universal first-order
thickening of `Z` over `Y` via `g : Z' ⟶ Y` and `f : Y ⟶ X` is formally
étale, then `i` is a universal first-order thickening of `Z` over `X`
via `g ≫ f`. -/
@[stacks 0604]
instance of_formallyEtale {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (i : Z ⟶ Z') (g : Z' ⟶ Y) (f : Y ⟶ X) [IsUniversalFirstOrder i g]
    [FormallyEtale f] : IsUniversalFirstOrder i (g ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
