module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Definition_100_8_1_Mono
public import stacks_project.Chap100.Lemma_100_11_1_Flat

/-!
# Monomorphisms into an fppf Spec(k)-cover of an algebraic stack

A monomorphism of algebraic stacks into a target that admits a locally finitely
presented, surjective, flat morphism from the spectrum of a field is either
empty or an equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 100.11.4: Let `f : Z' ⟶ Z` be a monomorphism of algebraic stacks.
Assume there exists a field `k` and a locally finitely presented, surjective,
flat morphism `cover : GroupoidsOver.slice (Over.mk σ) ⟶ Z` from
`Spec (.of k)`. Then either `IsEmpty (Points Z')` or
`(toBasedFunctor f).IsEquivalence`. -/
@[stacks 06MQ]
theorem isEmpty_or_isEquivalence_of_mono_of_spec_field_fppf {S : Scheme.{u}}
    {Z' Z : GroupoidsOver S} [AlgebraicStack Z'] [AlgebraicStack Z]
    (f : Z' ⟶ Z) [Groupoids.Hom.Mono f] {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} (cover : GroupoidsOver.slice (Over.mk σ) ⟶ Z)
    [Groupoids.Hom.LocallyOfFinitePresentation cover]
    [Groupoids.Hom.Surjective cover] [Groupoids.Hom.Flat cover] :
    IsEmpty (Points Z') ∨ (toBasedFunctor f).IsEquivalence :=
  sorry

/-- A monomorphism of algebraic stacks into a target admitting a locally finitely
presented, surjective, flat morphism from `Spec (.of k)` is an equivalence if
and only if the source is nonempty. -/
theorem isEquivalence_iff_nonempty_of_mono_of_spec_field_fppf {S : Scheme.{u}}
    {Z' Z : GroupoidsOver S} [AlgebraicStack Z'] [AlgebraicStack Z]
    (f : Z' ⟶ Z) [Groupoids.Hom.Mono f] {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} (cover : GroupoidsOver.slice (Over.mk σ) ⟶ Z)
    [Groupoids.Hom.LocallyOfFinitePresentation cover]
    [Groupoids.Hom.Surjective cover] [Groupoids.Hom.Flat cover] :
    (toBasedFunctor f).IsEquivalence ↔ Nonempty (Points Z') :=
  sorry

end AlgebraicGeometry.AlgebraicStack
