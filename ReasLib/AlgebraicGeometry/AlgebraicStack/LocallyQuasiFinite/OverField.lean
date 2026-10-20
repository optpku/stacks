module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map

/-!
# Locally quasi-finite morphisms of algebraic stacks over a field

A locally quasi-finite morphism from a scheme to an algebraic stack that is
locally quasi-finite over a field has locally quasi-finite scheme composite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite

/-- If an algebraic stack is locally quasi-finite over the spectrum of a field,
then the composite of a locally quasi-finite morphism from a scheme with this
structure morphism is locally of finite type and locally quasi-finite.
The scheme composite is identified with the composite of stack morphisms by
the given 2-isomorphism. -/
@[stacks 06UC]
theorem schemeHom_over_field {S : Scheme.{u}} {k : Type u} [Field k]
    {X : GroupoidsOver S} [AlgebraicStack X] (σ : Spec (.of k) ⟶ S)
    (π : X ⟶ GroupoidsOver.slice (Over.mk σ)) [LocallyQuasiFinite π]
    {V : Scheme.{u}} (τ : V ⟶ Spec (.of k))
    (f : GroupoidsOver.slice (Over.mk (τ ≫ σ)) ⟶ X) [LocallyQuasiFinite f]
    (h_comp : f ≫ π ≅ overMap (Over.homMk τ rfl)) :
    AlgebraicGeometry.LocallyOfFiniteType τ ∧ AlgebraicGeometry.LocallyQuasiFinite τ :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite
