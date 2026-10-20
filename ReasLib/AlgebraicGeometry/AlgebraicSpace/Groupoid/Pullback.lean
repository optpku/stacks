module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Pullback squares in groupoids in algebraic spaces

The projections and composition of a groupoid in algebraic spaces determine three
cartesian squares.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- The two projections from the algebraic space of composable arrows form a pullback square
with the source and target maps. -/
theorem fstSndIsPullback (G : GroupoidAlgebraicSpace B) :
    IsPullback (pullback.fst G.s G.t) (pullback.snd G.s G.t) G.s G.t := sorry

/-- Composition and the second projection form a pullback square over the source map. -/
theorem compSndIsPullback (G : GroupoidAlgebraicSpace B) :
    IsPullback G.c (pullback.snd G.s G.t) G.s G.s := sorry

/-- The first projection and composition form a pullback square over the target map. -/
theorem fstCompIsPullback (G : GroupoidAlgebraicSpace B) :
    IsPullback (pullback.fst G.s G.t) G.c G.t G.t := sorry

/-- The inverse of the first arrow and the second arrow of a common-target pair are composable. -/
theorem leftDivisionCondition (G : GroupoidAlgebraicSpace B) :
    (pullback.fst G.t G.t ≫ G.i) ≫ G.s = pullback.snd G.t G.t ≫ G.t := sorry

/-- For two arrows with a common target, compose the inverse of the first with the second. -/
def leftDivision (G : GroupoidAlgebraicSpace B) :
    pullback G.t G.t ⟶ G.R :=
  pullback.lift (pullback.fst G.t G.t ≫ G.i) (pullback.snd G.t G.t)
      (leftDivisionCondition G) ≫ G.c

/-- The source of a left quotient is the source of the second arrow. -/
theorem leftDivision_source (G : GroupoidAlgebraicSpace B) :
    G.leftDivision ≫ G.s = pullback.snd G.t G.t ≫ G.s := sorry

/-- The target of a left quotient is the source of the first arrow. -/
theorem leftDivision_target (G : GroupoidAlgebraicSpace B) :
    G.leftDivision ≫ G.t = pullback.fst G.t G.t ≫ G.s := sorry

/-- The first arrow and its left quotient form a composable pair. -/
theorem targetComparisonCondition (G : GroupoidAlgebraicSpace B) :
    pullback.fst G.t G.t ≫ G.s = G.leftDivision ≫ G.t := sorry

/-- The map `(pr₀, c ∘ (i, 1))` from common-target pairs to composable pairs. -/
def targetComparison (G : GroupoidAlgebraicSpace B) :
    pullback G.t G.t ⟶ pullback G.s G.t :=
  pullback.lift (pullback.fst G.t G.t) G.leftDivision (targetComparisonCondition G)

/-- The first projection of the target comparison is the first arrow. -/
theorem targetComparison_fst (G : GroupoidAlgebraicSpace B) :
    G.targetComparison ≫ pullback.fst G.s G.t = pullback.fst G.t G.t := sorry

/-- The second projection of the target comparison is left division. -/
theorem targetComparison_snd (G : GroupoidAlgebraicSpace B) :
    G.targetComparison ≫ pullback.snd G.s G.t = G.leftDivision := sorry

/-- Composing the first arrow with its left quotient recovers the second arrow. -/
theorem leftDivision_cancel (G : GroupoidAlgebraicSpace B) :
    G.targetComparison ≫ G.c = pullback.snd G.t G.t := sorry

/-- The first arrow of a composable pair and its composite have a common target. -/
theorem targetComparisonInvCondition (G : GroupoidAlgebraicSpace B) :
    pullback.fst G.s G.t ≫ G.t = G.c ≫ G.t := sorry

/-- The inverse comparison sends a composable pair to its first arrow and its composite. -/
def targetComparisonInv (G : GroupoidAlgebraicSpace B) :
    pullback G.s G.t ⟶ pullback G.t G.t :=
  pullback.lift (pullback.fst G.s G.t) G.c (targetComparisonInvCondition G)

/-- The first projection of the inverse comparison is the first arrow. -/
theorem targetComparisonInv_fst (G : GroupoidAlgebraicSpace B) :
    G.targetComparisonInv ≫ pullback.fst G.t G.t = pullback.fst G.s G.t := sorry

/-- The second projection of the inverse comparison is composition. -/
theorem targetComparisonInv_snd (G : GroupoidAlgebraicSpace B) :
    G.targetComparisonInv ≫ pullback.snd G.t G.t = G.c := sorry

/-- The target comparison followed by its inverse is the identity. -/
theorem targetComparison_hom_inv (G : GroupoidAlgebraicSpace B) :
    G.targetComparison ≫ G.targetComparisonInv = 𝟙 (pullback G.t G.t) := sorry

/-- The inverse comparison followed by the target comparison is the identity. -/
theorem targetComparison_inv_hom (G : GroupoidAlgebraicSpace B) :
    G.targetComparisonInv ≫ G.targetComparison = 𝟙 (pullback G.s G.t) := sorry

/-- The canonical isomorphism from common-target pairs to composable pairs. -/
def targetComparisonIso (G : GroupoidAlgebraicSpace B) :
    pullback G.t G.t ≅ pullback G.s G.t where
  hom := G.targetComparison
  inv := G.targetComparisonInv
  hom_inv_id := targetComparison_hom_inv G
  inv_hom_id := targetComparison_inv_hom G

/-- The forward map of `targetComparisonIso` is `(pr₀, c ∘ (i, 1))`. -/
theorem targetComparisonIso_hom (G : GroupoidAlgebraicSpace B) :
    G.targetComparisonIso.hom = G.targetComparison := sorry

/-- The inverse map of `targetComparisonIso` is `(pr₀, c)`. -/
theorem targetComparisonIso_inv (G : GroupoidAlgebraicSpace B) :
    G.targetComparisonIso.inv = G.targetComparisonInv := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
