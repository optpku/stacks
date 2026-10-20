module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat

/-!
# Field-spectrum morphisms into an algebraic stack with a flat surjective field cover

If an algebraic stack over a scheme admits one surjective flat morphism from the
spectrum of a field, then every morphism from the spectrum of a field is
surjective and flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- If an algebraic stack over a scheme admits a surjective flat morphism from
 the spectrum of a field, then every morphism from the spectrum of a field into
 that algebraic stack is surjective and flat. -/
theorem surjective_and_flat_of_specField_cover {S : Scheme.{u}} {Z : GroupoidsOver S}
    [AlgebraicStack Z] {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (cover : GroupoidsOver.slice (Over.mk σ) ⟶ Z)
    [Groupoids.Hom.Surjective cover] [Groupoids.Hom.Flat cover]
    {k' : Type u} [Field k'] {σ' : Spec (.of k') ⟶ S}
    (f : GroupoidsOver.slice (Over.mk σ') ⟶ Z) :
    Groupoids.Hom.Surjective f ∧ Groupoids.Hom.Flat f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
