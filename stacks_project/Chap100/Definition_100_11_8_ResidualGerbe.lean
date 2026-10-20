module

public import stacks_project.Chap100.Lemma_100_11_7
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe

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
by
  obtain ⟨ha, hr, hn, he, hs, hc, hf, hfaithful, hm, hi⟩ :=
    residualGerbe_properties X x
  exact ⟨ha, hr, hn, he, hs, ⟨hf, hfaithful⟩, hm, hi⟩

/-- Any strictly full inclusion of a reduced locally Noetherian singleton
algebraic stack into `X` whose image on points is `{x}` has the same essential
image as `residualGerbeι X x`. -/
theorem residualGerbeObjectProperty_unique {S : Scheme.{u}}
    {X Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Z] {x : Points X}
    [HasResidualGerbe X x] (ι : Z ⟶ X) [IsStrictlyFull ι] [IsReduced Z]
    [IsLocallyNoetherian Z] [Nonempty (Points Z)] [Subsingleton (Points Z)]
    (hι : Set.range (Points.map ι) = {x}) :
    (toFunctor ι).essImage = (toFunctor (residualGerbeι X x)).essImage :=
  residualGerbe_essImage_unique ι
    ⟨IsStrictlyFull.full, IsStrictlyFull.faithful⟩ hι

end AlgebraicGeometry.AlgebraicStack
