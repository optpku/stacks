module

public import stacks_project.Chap108.Lemma_108_4_8_Algebraic
public import stacks_project.Chap110.Lemma_110_53_1

/-!
# Surjective morphisms of CohStack-sized groupoid fibrations

A 1-morphism in `FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)`
is surjective when some scheme atlas of the source remains surjective after
composition, matching the atlas form of `AlgebraicStack.Surjective` at the
Hom-universe of `CohStack.toGroupoids`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

/-- A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over `Over S`, in
the Hom-universe of `CohStack.toGroupoids`, is surjective if some scheme atlas
of the source is surjective and remains surjective after composition. -/
class Surjective {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) : Prop where
  /-- There is a scheme `U` over `S` and a surjective 1-morphism
  `a : Classifying.slice U ⟶ X` such that `a ≫ f` is also surjective. -/
  exists_surjective_scheme_atlas :
    ∃ (U : Over S) (a : Classifying.slice U ⟶ X),
      Classifying.Surjective a ∧ Classifying.Surjective (a ≫ f)

/-- A 1-morphism is surjective if and only if some scheme atlas of the source is
surjective and remains surjective after composition. -/
theorem surjective_iff {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    Surjective f ↔
      ∃ (U : Over S) (a : Classifying.slice U ⟶ X),
        Classifying.Surjective a ∧ Classifying.Surjective (a ≫ f) :=
  sorry

namespace Surjective

/-- The identity 1-morphism of an algebraic stack is surjective. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] :
    Surjective (𝟙 X) :=
  sorry

/-- A surjective 1-morphism admits a scheme atlas of the source that remains
surjective after composition. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [Surjective f] :
    ∃ (U : Over S) (a : Classifying.slice U ⟶ X),
      Classifying.Surjective a ∧ Classifying.Surjective (a ≫ f) :=
  sorry

/-- A 1-morphism is surjective if and only if some scheme atlas of the source is
surjective and remains surjective after composition. -/
theorem iff {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    Surjective f ↔
      ∃ (U : Over S) (a : Classifying.slice U ⟶ X),
        Classifying.Surjective a ∧ Classifying.Surjective (a ≫ f) :=
  sorry

end Surjective

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
