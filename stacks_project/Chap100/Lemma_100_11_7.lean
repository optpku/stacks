module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Definition_100_8_1_Mono
public import stacks_project.Chap100.Lemma_100_9_10_Substack
public import stacks_project.Chap100.Lemma_100_11_1_Flat
public import stacks_project.Chap100.Lemma_100_11_2_Reduced
public import stacks_project.Chap100.Lemma_100_11_3_LocallyNoetherian

/-!
# Existence of a monomorphic singleton over a point

For an algebraic stack `X` and a point `x : Points X`, the existence of a
monomorphism from a singleton algebraic stack whose image is `{x}` is equivalent
to the reduced version of that existence, and to the existence of a monomorphism
together with a surjective flat field-valued point sent to `x`. When these hold,
there is a unique strictly full subcategory of `X` that is a reduced locally
Noetherian singleton mapping to `x`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- There exists an algebraic stack `Z` and a monomorphism `f : Z ⟶ X` such that
`Points Z` is a singleton and `Set.range (Points.map f) = {x}`. -/
def existsMonoSingletonAt {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) : Prop :=
  ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X),
    Groupoids.Hom.Mono f ∧ Nonempty (Points Z) ∧ Subsingleton (Points Z) ∧
      Set.range (Points.map f) = {x}

namespace existsMonoSingletonAt

/-- `existsMonoSingletonAt X x` unpacks to a monomorphism from a singleton
algebraic stack whose image on points is `{x}`. -/
theorem iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} :
    existsMonoSingletonAt X x ↔
      ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X),
        Groupoids.Hom.Mono f ∧ Nonempty (Points Z) ∧ Subsingleton (Points Z) ∧
          Set.range (Points.map f) = {x} :=
  sorry

/-- A monomorphism from a singleton algebraic stack with image `{x}` witnesses
`existsMonoSingletonAt`. -/
theorem of {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Z] {x : Points X} (f : Z ⟶ X) [Groupoids.Hom.Mono f]
    [Nonempty (Points Z)] [Subsingleton (Points Z)]
    (hx : Set.range (Points.map f) = {x}) : existsMonoSingletonAt X x :=
  sorry

/-- `existsMonoSingletonAt X x` supplies a monomorphism from a singleton
algebraic stack whose image on points is `{x}`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (h : existsMonoSingletonAt X x) :
    ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X),
      Groupoids.Hom.Mono f ∧ Nonempty (Points Z) ∧ Subsingleton (Points Z) ∧
        Set.range (Points.map f) = {x} :=
  sorry

end existsMonoSingletonAt

/-- There exists a reduced algebraic stack `Z` and a monomorphism `f : Z ⟶ X`
such that `Points Z` is a singleton and `Set.range (Points.map f) = {x}`. -/
def existsReducedMonoSingletonAt {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) : Prop :=
  ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X),
    Groupoids.Hom.Mono f ∧ IsReduced Z ∧ Nonempty (Points Z) ∧
      Subsingleton (Points Z) ∧ Set.range (Points.map f) = {x}

namespace existsReducedMonoSingletonAt

/-- `existsReducedMonoSingletonAt X x` unpacks to a monomorphism from a reduced
singleton algebraic stack whose image on points is `{x}`. -/
theorem iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} :
    existsReducedMonoSingletonAt X x ↔
      ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X),
        Groupoids.Hom.Mono f ∧ IsReduced Z ∧ Nonempty (Points Z) ∧
          Subsingleton (Points Z) ∧ Set.range (Points.map f) = {x} :=
  sorry

/-- A monomorphism from a reduced singleton algebraic stack with image `{x}`
witnesses `existsReducedMonoSingletonAt`. -/
theorem of {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Z] [IsReduced Z] {x : Points X} (f : Z ⟶ X)
    [Groupoids.Hom.Mono f] [Nonempty (Points Z)] [Subsingleton (Points Z)]
    (hx : Set.range (Points.map f) = {x}) :
    existsReducedMonoSingletonAt X x :=
  sorry

/-- `existsReducedMonoSingletonAt X x` supplies a monomorphism from a reduced
singleton algebraic stack whose image on points is `{x}`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (h : existsReducedMonoSingletonAt X x) :
    ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X),
      Groupoids.Hom.Mono f ∧ IsReduced Z ∧ Nonempty (Points Z) ∧
        Subsingleton (Points Z) ∧ Set.range (Points.map f) = {x} :=
  sorry

end existsReducedMonoSingletonAt

/-- There exists an algebraic stack `Z`, a monomorphism `f : Z ⟶ X`, and a
field-valued point `p : FieldValuedPoint Z` whose morphism is surjective and
flat, such that `Points.map f (Points.mk p) = x`. -/
def existsMonoSurjectiveFlatSpecFieldAt {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) : Prop :=
  ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X)
    (p : FieldValuedPoint Z),
    Groupoids.Hom.Mono f ∧ Groupoids.Hom.Surjective p.hom ∧
      Groupoids.Hom.Flat p.hom ∧ Points.map f (Points.mk p) = x

namespace existsMonoSurjectiveFlatSpecFieldAt

/-- `existsMonoSurjectiveFlatSpecFieldAt X x` unpacks to a monomorphism
`f : Z ⟶ X` and a surjective flat field-valued point of `Z` sent to `x`. -/
theorem iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} :
    existsMonoSurjectiveFlatSpecFieldAt X x ↔
      ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X)
        (p : FieldValuedPoint Z),
        Groupoids.Hom.Mono f ∧ Groupoids.Hom.Surjective p.hom ∧
          Groupoids.Hom.Flat p.hom ∧ Points.map f (Points.mk p) = x :=
  sorry

/-- A monomorphism together with a surjective flat field-valued point sent to
`x` witnesses `existsMonoSurjectiveFlatSpecFieldAt`. -/
theorem of {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Z] {x : Points X} (f : Z ⟶ X) (p : FieldValuedPoint Z)
    [Groupoids.Hom.Mono f] [Groupoids.Hom.Surjective p.hom]
    [Groupoids.Hom.Flat p.hom] (hx : Points.map f (Points.mk p) = x) :
    existsMonoSurjectiveFlatSpecFieldAt X x :=
  sorry

/-- `existsMonoSurjectiveFlatSpecFieldAt X x` supplies a monomorphism
`f : Z ⟶ X` and a surjective flat field-valued point of `Z` sent to `x`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (h : existsMonoSurjectiveFlatSpecFieldAt X x) :
    ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X)
      (p : FieldValuedPoint Z),
      Groupoids.Hom.Mono f ∧ Groupoids.Hom.Surjective p.hom ∧
        Groupoids.Hom.Flat p.hom ∧ Points.map f (Points.mk p) = x :=
  sorry

end existsMonoSurjectiveFlatSpecFieldAt

/-- Lemma 100.11.7 (1): Let `X` be an algebraic stack. Let `x : Points X` be a
point. The following are equivalent: there exists an algebraic stack `Z` and a
monomorphism `Z ⟶ X` such that `Points Z` is a singleton and the image of
`Points Z` in `Points X` is `x`; there exists a reduced algebraic stack `Z` and
a monomorphism `Z ⟶ X` such that `Points Z` is a singleton and the image of
`Points Z` in `Points X` is `x`; there exists an algebraic stack `Z`, a
monomorphism `f : Z ⟶ X`, and a surjective flat field-valued point
`p : FieldValuedPoint Z` such that `Points.map f (Points.mk p) = x`. -/
@[stacks 06MT]
theorem existsMonoSingletonAt_tfae {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) :
    List.TFAE
      [ existsMonoSingletonAt X x
      , existsReducedMonoSingletonAt X x
      , existsMonoSurjectiveFlatSpecFieldAt X x ] :=
  sorry

/-- Existence of a monomorphic singleton over `x` is equivalent to existence of
a reduced monomorphic singleton over `x`. -/
theorem existsMonoSingletonAt_iff_existsReducedMonoSingletonAt {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {x : Points X} :
    existsMonoSingletonAt X x ↔ existsReducedMonoSingletonAt X x :=
  sorry

/-- Existence of a monomorphic singleton over `x` is equivalent to existence of
a monomorphism together with a surjective flat field-valued point sent to `x`. -/
theorem existsMonoSingletonAt_iff_existsMonoSurjectiveFlatSpecFieldAt
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {x : Points X} :
    existsMonoSingletonAt X x ↔ existsMonoSurjectiveFlatSpecFieldAt X x :=
  sorry

/-- Existence of a reduced monomorphic singleton over `x` is equivalent to
existence of a monomorphism together with a surjective flat field-valued point
sent to `x`. -/
theorem existsReducedMonoSingletonAt_iff_existsMonoSurjectiveFlatSpecFieldAt
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {x : Points X} :
    existsReducedMonoSingletonAt X x ↔
      existsMonoSurjectiveFlatSpecFieldAt X x :=
  sorry

/-- Lemma 100.11.7 (2): If the equivalent conditions of Lemma 100.11.7 (1) hold
at `x`, then there exists a unique strictly full subcategory of `X`, as an
`ObjectProperty` of `X.total`, whose associated algebraic stack
`ofFunctor (P.ι ⋙ X.p)` is reduced, locally Noetherian, a singleton on points,
and maps to `x` via `Points.map (inclusionOf X P)`. Uniqueness is equality of
essential images of `inclusionOf`, not of a bundled pair `(Z, ι)`. -/
@[stacks 06MT]
theorem existsUnique_locallyNoetherian_strictlyFull_at {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X)
    (h : existsMonoSingletonAt X x) :
    ∃ (P : ObjectProperty X.total)
      (h_fibered : Functor.IsFibered.InGroupoids (P.ι ⋙ X.p))
      (h_algebraicStack : AlgebraicStack (ofFunctor (P.ι ⋙ X.p)))
      (h_reduced : IsReduced (ofFunctor (P.ι ⋙ X.p)))
      (h_locallyNoetherian : IsLocallyNoetherian (ofFunctor (P.ι ⋙ X.p)))
      (h_nonempty : Nonempty (Points (ofFunctor (P.ι ⋙ X.p))))
      (h_subsingleton : Subsingleton (Points (ofFunctor (P.ι ⋙ X.p))))
      (h_strictlyFull : IsStrictlyFull (inclusionOf X P))
      (h_image : Set.range (Points.map (inclusionOf X P)) = {x}),
      ∀ (Q : ObjectProperty X.total)
        (hQ_fibered : Functor.IsFibered.InGroupoids (Q.ι ⋙ X.p))
        (hQ_algebraicStack : AlgebraicStack (ofFunctor (Q.ι ⋙ X.p)))
        (hQ_reduced : IsReduced (ofFunctor (Q.ι ⋙ X.p)))
        (hQ_locallyNoetherian : IsLocallyNoetherian (ofFunctor (Q.ι ⋙ X.p)))
        (hQ_nonempty : Nonempty (Points (ofFunctor (Q.ι ⋙ X.p))))
        (hQ_subsingleton : Subsingleton (Points (ofFunctor (Q.ι ⋙ X.p))))
        (hQ_strictlyFull : IsStrictlyFull (inclusionOf X Q))
        (hQ_image : Set.range (Points.map (inclusionOf X Q)) = {x}),
        (toFunctor (inclusionOf X Q)).essImage =
          (toFunctor (inclusionOf X P)).essImage :=
  sorry

/-- Any two strictly full inclusions of reduced locally Noetherian singleton
algebraic stacks into `X` whose images on points are `{x}` have the same
essential image. -/
theorem unique_locallyNoetherian_strictlyFull_at {S : Scheme.{u}}
    {X Z Z' : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Z]
    [AlgebraicStack Z'] {x : Points X} (ι : Z ⟶ X) (ι' : Z' ⟶ X)
    [IsStrictlyFull ι] [IsStrictlyFull ι']
    [IsReduced Z] [IsReduced Z']
    [IsLocallyNoetherian Z] [IsLocallyNoetherian Z']
    [Nonempty (Points Z)] [Nonempty (Points Z')]
    [Subsingleton (Points Z)] [Subsingleton (Points Z')]
    (hι : Set.range (Points.map ι) = {x})
    (hι' : Set.range (Points.map ι') = {x}) :
    (toFunctor ι).essImage = (toFunctor ι').essImage :=
  sorry

end AlgebraicGeometry.AlgebraicStack
