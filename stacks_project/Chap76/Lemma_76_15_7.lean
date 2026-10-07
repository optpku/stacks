module

public import stacks_project.Chap76.«76_15_0_1_Universal»
public import stacks_project.Chap76.Lemma_76_14_4_FormallyUnramified

/-!
# Universal first-order thickenings of formally unramified morphisms

If `Z ⟶ X` is formally unramified, then the ambient map of a universal
first-order thickening of `Z` over `X` is formally unramified.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder

/-- Lemma 76.15.7: Let `S` be a scheme. Let `Z ⟶ X` be a formally unramified
morphism of algebraic spaces over `S`. Then the universal first-order
thickening `Z'` is formally unramified over `X`. -/
@[stacks 0609]
theorem formallyUnramified {S : Scheme.{u}} {X Z Z' : AlgebraicSpace S}
    (i : Z ⟶ Z') (f : Z' ⟶ X) [IsUniversalFirstOrder i f]
    [FormallyUnramified (i ≫ f)] : FormallyUnramified f :=
  sorry

/-- If `h : Z ⟶ X` is formally unramified and `i : Z ⟶ Z'` is a universal
first-order thickening of `Z` over `X` via `f : Z' ⟶ X` with `i ≫ f = h`,
then `f` is formally unramified. -/
theorem formallyUnramified_of {S : Scheme.{u}} {Z X Z' : AlgebraicSpace S}
    (h : Z ⟶ X) (i : Z ⟶ Z') (f : Z' ⟶ X) [FormallyUnramified h]
    [IsUniversalFirstOrder i f] (w : i ≫ f = h) : FormallyUnramified f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
