module

public import stacks_project.Chap101.Definition_101_23_2_LocallyQuasiFinite
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map

/-!
# Locally quasi-finite morphisms of algebraic stacks over a field

A locally quasi-finite morphism from a scheme to an algebraic stack that is
itself locally quasi-finite over the spectrum of a field remains locally
quasi-finite over that spectrum.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace LocallyQuasiFinite

/-- Lemma 101.23.4: If `X` is an algebraic stack, `k` is a field, and
`π : X ⟶ GroupoidsOver.slice (Over.mk σ)` is locally quasi-finite, then a
locally quasi-finite morphism `f` from the slice of a scheme `V` over
`Spec (.of k)`, identified with a scheme morphism `τ : V ⟶ Spec (.of k)` by
a 2-isomorphism `f ≫ π ≅ overMap (Over.homMk τ rfl)`, has `τ` locally
quasi-finite.

Stacks locally quasi-finite is the conjunction
`AlgebraicGeometry.LocallyOfFiniteType τ ∧ AlgebraicGeometry.LocallyQuasiFinite τ`,
as in Lemma 72.10.9. -/
@[stacks 06UC]
theorem schemeHom_over_field {S : Scheme.{u}} {k : Type u} [Field k]
    {X : GroupoidsOver S} [AlgebraicStack X] (σ : Spec (.of k) ⟶ S)
    (π : X ⟶ GroupoidsOver.slice (Over.mk σ)) [LocallyQuasiFinite π]
    {V : Scheme.{u}} (τ : V ⟶ Spec (.of k))
    (f : GroupoidsOver.slice (Over.mk (τ ≫ σ)) ⟶ X) [LocallyQuasiFinite f]
    (h_comp : f ≫ π ≅ overMap (Over.homMk τ rfl)) :
    AlgebraicGeometry.LocallyOfFiniteType τ ∧ AlgebraicGeometry.LocallyQuasiFinite τ :=
  sorry

/-- The scheme morphism `τ : V ⟶ Spec (.of k)` identified with the composite
`f ≫ π` is locally of finite type. -/
theorem schemeHom_over_field_locallyOfFiniteType {S : Scheme.{u}} {k : Type u}
    [Field k] {X : GroupoidsOver S} [AlgebraicStack X]
    (σ : Spec (.of k) ⟶ S) (π : X ⟶ GroupoidsOver.slice (Over.mk σ))
    [LocallyQuasiFinite π] {V : Scheme.{u}} (τ : V ⟶ Spec (.of k))
    (f : GroupoidsOver.slice (Over.mk (τ ≫ σ)) ⟶ X) [LocallyQuasiFinite f]
    (h_comp : f ≫ π ≅ overMap (Over.homMk τ rfl)) :
    AlgebraicGeometry.LocallyOfFiniteType τ :=
  sorry

end LocallyQuasiFinite

end AlgebraicGeometry.AlgebraicStack
