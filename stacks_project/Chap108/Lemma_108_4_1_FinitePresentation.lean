module

public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap110.Lemma_110_53_1

/-!
# Finite-presentation morphisms of CohStack-sized groupoid fibrations

A 1-morphism in `FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)`
is of finite presentation when it is representable by algebraic spaces and every
representing morphism `fy : Fy ⟶ ofOver U` is of finite presentation as a
morphism of algebraic spaces, matching the Isom ⟶ T finite-presentation test at
the Hom-universe of `CohStack.toGroupoids`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

/-- A 1-morphism of categories fibred in groupoids over `Over S`, in the
Hom-universe of `CohStack.toGroupoids`, is of finite presentation when it is
representable by algebraic spaces and every representing morphism
`fy : Fy ⟶ ofOver U` is of finite presentation as a morphism of algebraic
spaces. -/
class FinitePresentation {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) : Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : Classifying.relativelyRepresentableByAlgebraicSpaces f
  /-- Every representing morphism of algebraic spaces is of finite presentation. -/
  of_represents : ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ Y)
    (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    Classifying.RepresentsBaseChange f y Fy fy →
      AlgebraicSpace.FinitePresentation fy

namespace FinitePresentation

/-- The identity 1-morphism of a category fibred in groupoids is of finite
presentation. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)} :
    FinitePresentation (𝟙 X) :=
  sorry

/-- A representing morphism of algebraic spaces for a finite-presentation
1-morphism of groupoid fibrations is of finite presentation. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [FinitePresentation f] {U : Over S}
    (y : Classifying.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U}
    (h : Classifying.RepresentsBaseChange f y Fy fy) :
    AlgebraicSpace.FinitePresentation fy :=
  sorry

/-- A finite-presentation 1-morphism of groupoid fibrations is representable by
algebraic spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [FinitePresentation f] :
    Classifying.relativelyRepresentableByAlgebraicSpaces f :=
  sorry

/-- A 1-morphism is of finite presentation if and only if it is representable by
algebraic spaces and every representing morphism of algebraic spaces is of
finite presentation. -/
theorem iff {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    FinitePresentation f ↔
      Classifying.relativelyRepresentableByAlgebraicSpaces f ∧
        ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ Y) (Fy : AlgebraicSpace S)
          (fy : Fy ⟶ AlgebraicSpace.ofOver U),
          Classifying.RepresentsBaseChange f y Fy fy →
            AlgebraicSpace.FinitePresentation fy :=
  sorry

end FinitePresentation

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
