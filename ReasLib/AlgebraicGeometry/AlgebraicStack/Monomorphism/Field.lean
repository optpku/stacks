module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Monomorphism
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat

/-!
# Monomorphisms into algebraic stacks covered by a field spectrum

A monomorphism of algebraic stacks into a target admitting a locally finitely
presented, surjective, flat morphism from the spectrum of a field has empty
source or is an equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A monomorphism of algebraic stacks into a target admitting a locally finitely
presented, surjective, flat morphism from the spectrum of a field has empty
source or is an equivalence over the base scheme. -/
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
presented, surjective, flat morphism from the spectrum of a field is an
equivalence over the base scheme if and only if its source has a point. -/
theorem isEquivalence_iff_nonempty_of_mono_of_spec_field_fppf {S : Scheme.{u}}
    {Z' Z : GroupoidsOver S} [AlgebraicStack Z'] [AlgebraicStack Z]
    (f : Z' ⟶ Z) [Groupoids.Hom.Mono f] {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} (cover : GroupoidsOver.slice (Over.mk σ) ⟶ Z)
    [Groupoids.Hom.LocallyOfFinitePresentation cover]
    [Groupoids.Hom.Surjective cover] [Groupoids.Hom.Flat cover] :
    (toBasedFunctor f).IsEquivalence ↔ Nonempty (Points Z') :=
  sorry

end AlgebraicGeometry.AlgebraicStack
