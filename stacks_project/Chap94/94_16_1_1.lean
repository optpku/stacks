module

public import stacks_project.Chap94.«94_16_1_1_CanonicalHom»

/-!
# Canonical action of `f_can` on morphisms

Special-case formula for the morphism `f_can : [U/R] ⟶ X` on arrows of `[U/R]`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- 94.16.1.1: in the special-case description of `f_can : [U/R] ⟶ X` from
lemma 04T4, a morphism `φ : a ⟶ b` in `[U/R]` over `T` is an object
`φ = (b, a, α)` of the self 2-fibre product `R` of `f` over `T` (note the
switch), and `f_can(φ)` is the fibre morphism `f(a) ⟶ f(b)` given by `α⁻¹`. -/
@[stacks 04TG]
theorem canonicalHom_eq_inv {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)
    {T : Over S} (a b : U.p.Fiber T)
    (α : (fiberFunctor f T).obj b ≅ (fiberFunctor f T).obj a) :
    canonicalHom f (ofSwitchedComparison f a b α) = α.inv :=
  sorry

end AlgebraicGeometry
