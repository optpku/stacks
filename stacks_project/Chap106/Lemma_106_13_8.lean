module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import stacks_project.Chap94.Definition_94_12_2_Etale
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_10_1_Integral
public import stacks_project.Chap101.Lemma_101_5_1
public import stacks_project.Chap101.Lemma_101_45_5_Comparison
public import stacks_project.Chap106.Definition_106_13_1_WellNighAffine

/-!
# Étale-local well-nigh affine covers of algebraic stacks with finite inertia

If the inertia morphism of an algebraic stack is finite, the stack admits a
covering by morphisms from well-nigh affine algebraic stacks that are
representable by algebraic spaces, separated, and étale, and that induce an
isomorphism on inertia comparisons.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- There exists a family of morphisms of algebraic stacks covering `|X|`,
each with well-nigh affine source, inducing an isomorphism of inertia stacks
via `Inertia.comparison`, and representable by algebraic spaces, separated,
and étale. -/
def existsEtaleLocalWellNighAffineCover {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : Prop :=
  ∃ (I : Type (u + 1)) (Xi : I → GroupoidsOver S)
      (_ : ∀ i, AlgebraicStack (Xi i)) (g : ∀ i, Xi i ⟶ X),
    (⋃ i, Set.range (Points.map (g i))) = Set.univ ∧
      ∀ i, IsWellNighAffine (Xi i) ∧
        (toBasedFunctor (Inertia.comparison (g i))).IsEquivalence ∧
        relativelyRepresentableByAlgebraicSpaces (g i) ∧ Separated (g i) ∧
          Groupoids.Hom.Etale (g i)

namespace existsEtaleLocalWellNighAffineCover

/-- `existsEtaleLocalWellNighAffineCover X` unpacks to a covering family of
étale, separated, space-representable morphisms from well-nigh affine algebraic
stacks whose inertia comparisons are equivalences. -/
theorem iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    existsEtaleLocalWellNighAffineCover X ↔
      ∃ (I : Type (u + 1)) (Xi : I → GroupoidsOver S)
          (_ : ∀ i, AlgebraicStack (Xi i)) (g : ∀ i, Xi i ⟶ X),
        (⋃ i, Set.range (Points.map (g i))) = Set.univ ∧
          ∀ i, IsWellNighAffine (Xi i) ∧
            (toBasedFunctor (Inertia.comparison (g i))).IsEquivalence ∧
            relativelyRepresentableByAlgebraicSpaces (g i) ∧ Separated (g i) ∧
              Groupoids.Hom.Etale (g i) :=
  sorry

/-- A covering family of étale, separated, space-representable morphisms from
well-nigh affine algebraic stacks whose inertia comparisons are equivalences
witnesses `existsEtaleLocalWellNighAffineCover X`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (I : Type (u + 1)) (Xi : I → GroupoidsOver S) [∀ i, AlgebraicStack (Xi i)]
    (g : ∀ i, Xi i ⟶ X)
    (h_cover : (⋃ i, Set.range (Points.map (g i))) = Set.univ)
    [∀ i, IsWellNighAffine (Xi i)]
    [∀ i, (toBasedFunctor (Inertia.comparison (g i))).IsEquivalence]
    (h_repr : ∀ i, relativelyRepresentableByAlgebraicSpaces (g i))
    [∀ i, Separated (g i)] [∀ i, Groupoids.Hom.Etale (g i)] :
    existsEtaleLocalWellNighAffineCover X :=
  sorry

/-- `existsEtaleLocalWellNighAffineCover X` supplies a covering family of
étale, separated, space-representable morphisms from well-nigh affine algebraic
stacks whose inertia comparisons are equivalences. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : existsEtaleLocalWellNighAffineCover X) :
    ∃ (I : Type (u + 1)) (Xi : I → GroupoidsOver S)
        (_ : ∀ i, AlgebraicStack (Xi i)) (g : ∀ i, Xi i ⟶ X),
      (⋃ i, Set.range (Points.map (g i))) = Set.univ ∧
        ∀ i, IsWellNighAffine (Xi i) ∧
          (toBasedFunctor (Inertia.comparison (g i))).IsEquivalence ∧
          relativelyRepresentableByAlgebraicSpaces (g i) ∧ Separated (g i) ∧
            Groupoids.Hom.Etale (g i) :=
  sorry

end existsEtaleLocalWellNighAffineCover

/-- Lemma 106.13.8: Let `X` be an algebraic stack. Assume the inertia morphism
`forget X : I_X ⟶ X` is finite. Then there exist a set `I` and morphisms of
algebraic stacks `g i : Xi i ⟶ X` such that `|X|` is the union of the images
`|g i|(|Xi i|)`, each `Xi i` is well-nigh affine, each inertia comparison
`I_{Xi i} ⟶ Xi i ×_X I_X` is an isomorphism, and each `g i` is representable
by algebraic spaces, separated, and étale. -/
@[stacks 0DUE]
theorem existsEtaleLocalWellNighAffineCover_of_isFinite_inertia
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsFinite (forget.{u + 1, u, u, u + 1} X)] :
    existsEtaleLocalWellNighAffineCover X :=
  sorry

/-- Under the finite-inertia hypothesis of Lemma 106.13.8, every point of `|X|`
lies in the image of an étale, separated, space-representable morphism from a
well-nigh affine algebraic stack whose inertia comparison is an isomorphism. -/
theorem existsEtaleLocalWellNighAffineChartAt {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X]
    [IsFinite (forget.{u + 1, u, u, u + 1} X)] (x : Points X) :
    ∃ (Xi : GroupoidsOver S) (_ : AlgebraicStack Xi) (g : Xi ⟶ X)
      (xi : Points Xi),
      Points.map g xi = x ∧ IsWellNighAffine Xi ∧
        (toBasedFunctor (Inertia.comparison g)).IsEquivalence ∧
        relativelyRepresentableByAlgebraicSpaces g ∧ Separated g ∧
          Groupoids.Hom.Etale g :=
  sorry

end AlgebraicGeometry.AlgebraicStack
