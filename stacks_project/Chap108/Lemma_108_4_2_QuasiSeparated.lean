module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap108.Lemma_108_4_1_Diagonal
public import stacks_project.Chap110.Lemma_110_53_1

/-!
# Quasi-separated morphisms of CohStack-sized groupoid fibrations

A 1-morphism in `FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)`
is quasi-separated when its relative 2-diagonal is representable by algebraic
spaces and every representing morphism of that diagonal is quasi-compact and
quasi-separated, matching Definition 101.4.1 at the Hom-universe of
`CohStack.toGroupoids`.
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
the Hom-universe of `CohStack.toGroupoids`, has a morphism property `P` of
algebraic spaces when every scheme-slice representing morphism
`fy : Fy ⟶ AlgebraicSpace.ofOver U` satisfies `P`. -/
def has {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (P : MorphismProperty (AlgebraicSpace S)) (f : X ⟶ Y) : Prop :=
  ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ Y) (Fy : AlgebraicSpace S)
    (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    Classifying.RepresentsBaseChange f y Fy fy → P fy

/-- A 1-morphism has `P` if and only if every scheme-slice representing morphism
of algebraic spaces has `P`. -/
theorem has_iff {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (P : MorphismProperty (AlgebraicSpace S)) (f : X ⟶ Y) :
    has P f ↔
      ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ Y) (Fy : AlgebraicSpace S)
        (fy : Fy ⟶ AlgebraicSpace.ofOver U),
        Classifying.RepresentsBaseChange f y Fy fy → P fy :=
  sorry

namespace has

/-- A scheme-slice representing morphism of algebraic spaces for a 1-morphism
that has `P` itself has `P`. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    {P : MorphismProperty (AlgebraicSpace S)} {f : X ⟶ Y} (hf : has P f)
    {U : Over S} (y : Classifying.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U}
    (h : Classifying.RepresentsBaseChange f y Fy fy) : P fy :=
  sorry

/-- A 1-morphism has `P` if every scheme-slice representing morphism of algebraic
spaces has `P`. -/
theorem of {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    {P : MorphismProperty (AlgebraicSpace S)} {f : X ⟶ Y}
    (h : ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ Y) (Fy : AlgebraicSpace S)
      (fy : Fy ⟶ AlgebraicSpace.ofOver U),
      Classifying.RepresentsBaseChange f y Fy fy → P fy) : has P f :=
  sorry

end has

/-- A 1-morphism of categories fibred in groupoids over `Over S`, in the
Hom-universe of `CohStack.toGroupoids`, is quasi-separated when its relative
2-diagonal is representable by algebraic spaces and both quasi-compact and
quasi-separated on scheme-slice representing morphisms. -/
class QuasiSeparated {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) : Prop where
  /-- The relative 2-diagonal is representable by algebraic spaces. -/
  representable_diagonal :
    Classifying.relativelyRepresentableByAlgebraicSpaces (diagonal f)
  /-- The relative 2-diagonal is quasi-compact. -/
  quasiCompact_diagonal : has (@AlgebraicSpace.QuasiCompact S) (diagonal f)
  /-- The relative 2-diagonal is quasi-separated. -/
  quasiSeparated_diagonal : has (@AlgebraicSpace.QuasiSeparated S) (diagonal f)

namespace QuasiSeparated

/-- The identity 1-morphism of a category fibred in groupoids is
quasi-separated. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)} :
    QuasiSeparated (𝟙 X) :=
  sorry

/-- A 1-morphism is quasi-separated if and only if its relative 2-diagonal is
representable by algebraic spaces and both quasi-compact and quasi-separated. -/
theorem iff {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    QuasiSeparated f ↔
      Classifying.relativelyRepresentableByAlgebraicSpaces (diagonal f) ∧
        has (@AlgebraicSpace.QuasiCompact S) (diagonal f) ∧
          has (@AlgebraicSpace.QuasiSeparated S) (diagonal f) :=
  sorry

/-- The relative 2-diagonal of a quasi-separated 1-morphism is representable by
algebraic spaces and both quasi-compact and quasi-separated. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [QuasiSeparated f] :
    Classifying.relativelyRepresentableByAlgebraicSpaces (diagonal f) ∧
      has (@AlgebraicSpace.QuasiCompact S) (diagonal f) ∧
        has (@AlgebraicSpace.QuasiSeparated S) (diagonal f) :=
  sorry

end QuasiSeparated

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
