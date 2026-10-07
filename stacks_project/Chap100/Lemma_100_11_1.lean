module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Lemma_100_11_1_Flat

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

namespace AlgebraicGeometry.Groupoids.Hom

namespace Surjective

/-- Lemma 100.11.1 (1): Let `S` be a scheme and let `Z` be an algebraic stack over
`S`. If `k` is a field and `cover : GroupoidsOver.slice (Over.mk σ) ⟶ Z` is a
surjective flat morphism from `Spec (.of k)`, then any morphism
`f : GroupoidsOver.slice (Over.mk σ') ⟶ Z` from `Spec (.of k')` with `k'` a
field is surjective. -/
@[stacks 06MM]
theorem of_specField_cover {S : Scheme.{u}} {Z : GroupoidsOver S}
    [AlgebraicStack Z] {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (cover : GroupoidsOver.slice (Over.mk σ) ⟶ Z) [Surjective cover] [Flat cover]
    {k' : Type u} [Field k'] {σ' : Spec (.of k') ⟶ S}
    (f : GroupoidsOver.slice (Over.mk σ') ⟶ Z) : Surjective f :=
  sorry

end Surjective

namespace Flat

/-- Lemma 100.11.1 (2): Let `S` be a scheme and let `Z` be an algebraic stack over
`S`. If `k` is a field and `cover : GroupoidsOver.slice (Over.mk σ) ⟶ Z` is a
surjective flat morphism from `Spec (.of k)`, then any morphism
`f : GroupoidsOver.slice (Over.mk σ') ⟶ Z` from `Spec (.of k')` with `k'` a
field is flat. -/
@[stacks 06MM]
theorem of_specField_cover {S : Scheme.{u}} {Z : GroupoidsOver S}
    [AlgebraicStack Z] {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (cover : GroupoidsOver.slice (Over.mk σ) ⟶ Z) [Surjective cover] [Flat cover]
    {k' : Type u} [Field k'] {σ' : Spec (.of k') ⟶ S}
    (f : GroupoidsOver.slice (Over.mk σ') ⟶ Z) : Flat f :=
  sorry

end Flat

end AlgebraicGeometry.Groupoids.Hom
