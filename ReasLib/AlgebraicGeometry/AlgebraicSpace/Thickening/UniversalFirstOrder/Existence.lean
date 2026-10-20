module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyUnramified

/-!
# Existence of universal first-order thickenings

A formally unramified morphism of algebraic spaces over a scheme admits a
universal first-order thickening.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder

/-- A formally unramified morphism `h : Z ⟶ X` of algebraic spaces over a scheme
factors as `i ≫ f = h`, where `i : Z ⟶ Z'` is a universal first-order thickening
of `Z` over `X` via `f : Z' ⟶ X`. -/
@[stacks 0606]
theorem exists_of_formallyUnramified {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (h : Z ⟶ X) [FormallyUnramified h] :
    ∃ (Z' : AlgebraicSpace S) (i : Z ⟶ Z') (f : Z' ⟶ X),
      i ≫ f = h ∧ IsUniversalFirstOrder i f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
