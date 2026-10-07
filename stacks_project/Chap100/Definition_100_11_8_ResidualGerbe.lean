module

public import stacks_project.Chap100.Lemma_100_11_7

/-!
# Residual gerbes of algebraic stacks

The residual gerbe of an algebraic stack `X` at a point `x` exists exactly when
the equivalent conditions of Lemma 100.11.7 hold. If it exists, it is the unique
strictly full subcategory of `X` that is a reduced locally Noetherian singleton
mapping to `x`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The residual gerbe of an algebraic stack `X` at a point `x` exists if the
equivalent conditions of Lemma 100.11.7 hold. -/
@[mk_iff]
class HasResidualGerbe {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (x : Points X) : Prop where
  /-- There is a monomorphism from a singleton algebraic stack whose image on
  points is `{x}`. -/
  exists_mono_singleton : existsMonoSingletonAt X x

namespace HasResidualGerbe

/-- If the residual gerbe of `X` at `x` exists, then there is a monomorphism from
a singleton algebraic stack whose image on points is `{x}`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} [HasResidualGerbe X x] : existsMonoSingletonAt X x :=
  sorry

/-- The residual gerbe of `X` at `x` exists if and only if there is a
monomorphism from a singleton algebraic stack whose image on points is `{x}`. -/
theorem iff_existsMonoSingletonAt {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} :
    HasResidualGerbe X x ↔ existsMonoSingletonAt X x :=
  sorry

/-- The residual gerbe of `X` at `x` exists if and only if there is a
monomorphism from a reduced singleton algebraic stack whose image on points is
`{x}`. -/
theorem iff_existsReducedMonoSingletonAt {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} :
    HasResidualGerbe X x ↔ existsReducedMonoSingletonAt X x :=
  sorry

/-- The residual gerbe of `X` at `x` exists if and only if there is a
monomorphism together with a surjective flat field-valued point sent to `x`. -/
theorem iff_existsMonoSurjectiveFlatSpecFieldAt {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {x : Points X} :
    HasResidualGerbe X x ↔ existsMonoSurjectiveFlatSpecFieldAt X x :=
  sorry

/-- A monomorphism from a singleton algebraic stack whose image on points is
`{x}` witnesses that the residual gerbe of `X` at `x` exists. -/
theorem of_mono {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Z] {x : Points X} (f : Z ⟶ X) [Groupoids.Hom.Mono f]
    [Nonempty (Points Z)] [Subsingleton (Points Z)]
    (hx : Set.range (Points.map f) = {x}) : HasResidualGerbe X x :=
  sorry

end HasResidualGerbe

/-- A nonempty singleton algebraic stack has a residual gerbe at each of its
points, given by the identity 1-morphism. -/
instance instHasResidualGerbe_of_subsingleton_points {S : Scheme.{u}}
    (Z : GroupoidsOver S) [AlgebraicStack Z] [Nonempty (Points Z)]
    [Subsingleton (Points Z)] {x : Points Z} : HasResidualGerbe Z x where
  exists_mono_singleton := existsMonoSingletonAt.of (𝟙 Z) sorry

/-- The unique strictly full subcategory of `X` at `x` supplied by
Lemma 100.11.7 (2), as an `ObjectProperty` of `X.total`. -/
noncomputable def residualGerbeObjectProperty {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X)
    [HasResidualGerbe X x] : ObjectProperty X.total :=
  Classical.choose
    (existsUnique_locallyNoetherian_strictlyFull_at X x
      HasResidualGerbe.exists_mono_singleton)

/-- The residual-gerbe subcategory of `X` at `x` is fibred in groupoids over
`Over S`. -/
noncomputable instance instIsFiberedInGroupoids_residualGerbeObjectProperty
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X)
    [HasResidualGerbe X x] :
    Functor.IsFibered.InGroupoids
      ((residualGerbeObjectProperty X x).ι ⋙ X.p) :=
  Classical.choose
    (Classical.choose_spec
      (existsUnique_locallyNoetherian_strictlyFull_at X x
        HasResidualGerbe.exists_mono_singleton))

/-- The residual gerbe of `X` at `x`, as the strictly full subcategory of `X`
constructed in Lemma 100.11.7. -/
abbrev residualGerbe {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (x : Points X) [HasResidualGerbe X x] : GroupoidsOver S :=
  ofFunctor ((residualGerbeObjectProperty X x).ι ⋙ X.p)

/-- The canonical strictly full inclusion of the residual gerbe of `X` at `x`. -/
abbrev residualGerbeι {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (x : Points X) [HasResidualGerbe X x] : residualGerbe X x ⟶ X :=
  inclusionOf X (residualGerbeObjectProperty X x)

/-- The residual gerbe of `X` at `x` is an algebraic stack. -/
instance instAlgebraicStack_residualGerbe {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) [HasResidualGerbe X x] :
    AlgebraicStack (residualGerbe X x) :=
  sorry

/-- The residual gerbe of `X` at `x` is reduced. -/
instance instIsReduced_residualGerbe {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) [HasResidualGerbe X x] :
    IsReduced (residualGerbe X x) :=
  sorry

/-- The residual gerbe of `X` at `x` is locally Noetherian. -/
instance instIsLocallyNoetherian_residualGerbe {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X)
    [HasResidualGerbe X x] : IsLocallyNoetherian (residualGerbe X x) :=
  sorry

/-- The residual gerbe of `X` at `x` is nonempty on points. -/
instance instNonempty_points_residualGerbe {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X)
    [HasResidualGerbe X x] : Nonempty (Points (residualGerbe X x)) :=
  sorry

/-- The residual gerbe of `X` at `x` is a singleton on points. -/
instance instSubsingleton_points_residualGerbe {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X)
    [HasResidualGerbe X x] : Subsingleton (Points (residualGerbe X x)) :=
  sorry

/-- The residual-gerbe inclusion is a monomorphism. -/
instance instMono_residualGerbeι {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) [HasResidualGerbe X x] :
    Groupoids.Hom.Mono (residualGerbeι X x) :=
  sorry

/-- The residual gerbe of `X` at `x` is a reduced locally Noetherian singleton
algebraic stack, and `residualGerbeι X x` is a strictly full monomorphism whose
image on points is `{x}`. -/
theorem residualGerbe_spec {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) [HasResidualGerbe X x] :
    AlgebraicStack (residualGerbe X x) ∧ IsReduced (residualGerbe X x) ∧
      IsLocallyNoetherian (residualGerbe X x) ∧
      Nonempty (Points (residualGerbe X x)) ∧
      Subsingleton (Points (residualGerbe X x)) ∧
      IsStrictlyFull (residualGerbeι X x) ∧
      Groupoids.Hom.Mono (residualGerbeι X x) ∧
      Set.range (Points.map (residualGerbeι X x)) = {x} :=
  sorry

/-- Any strictly full inclusion of a reduced locally Noetherian singleton
algebraic stack into `X` whose image on points is `{x}` has the same essential
image as `residualGerbeι X x`. -/
theorem residualGerbeObjectProperty_unique {S : Scheme.{u}}
    {X Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Z] {x : Points X}
    [HasResidualGerbe X x] (ι : Z ⟶ X) [IsStrictlyFull ι] [IsReduced Z]
    [IsLocallyNoetherian Z] [Nonempty (Points Z)] [Subsingleton (Points Z)]
    (hι : Set.range (Points.map ι) = {x}) :
    (toFunctor ι).essImage = (toFunctor (residualGerbeι X x)).essImage :=
  sorry

end AlgebraicGeometry.AlgebraicStack
