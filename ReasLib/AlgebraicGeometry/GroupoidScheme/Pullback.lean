module

public import ReasLib.AlgebraicGeometry.GroupoidScheme

/-!
# Pullback squares in groupoid schemes

This module records the cartesian squares determined by the projections and composition of a
groupoid scheme.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The inverse of the first arrow and the second arrow of a common-target pair are composable. -/
theorem leftDivisionCondition {S : Scheme.{u}} (G : GroupoidScheme S) :
    (pullback.fst G.t G.t ≫ G.i) ≫ G.s = pullback.snd G.t G.t ≫ G.t := sorry

/-- For two arrows with a common target, compose the inverse of the first with the second. -/
def leftDivision {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback G.t G.t ⟶ G.R :=
  pullback.lift (pullback.fst G.t G.t ≫ G.i) (pullback.snd G.t G.t)
      (leftDivisionCondition G) ≫ G.c

/-- The source of a left quotient is the source of the second arrow. -/
theorem leftDivision_source {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.leftDivision ≫ G.s = pullback.snd G.t G.t ≫ G.s := sorry

/-- The target of a left quotient is the source of the first arrow. -/
theorem leftDivision_target {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.leftDivision ≫ G.t = pullback.fst G.t G.t ≫ G.s := sorry

/-- The first arrow and its left quotient form a composable pair. -/
theorem targetComparisonCondition {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback.fst G.t G.t ≫ G.s = G.leftDivision ≫ G.t := sorry

/-- The map `(pr₀, c ∘ (i, 1))` from common-target pairs to composable pairs. -/
def targetComparison {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback G.t G.t ⟶ pullback G.s G.t :=
  pullback.lift (pullback.fst G.t G.t) G.leftDivision (targetComparisonCondition G)

/-- The first projection of the target comparison is the first arrow. -/
theorem targetComparison_fst {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.targetComparison ≫ pullback.fst G.s G.t = pullback.fst G.t G.t := sorry

/-- The second projection of the target comparison is left division. -/
theorem targetComparison_snd {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.targetComparison ≫ pullback.snd G.s G.t = G.leftDivision := sorry

/-- Composing the first arrow with its left quotient recovers the second arrow. -/
theorem leftDivision_cancel {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.targetComparison ≫ G.c = pullback.snd G.t G.t := sorry

/-- The first arrow of a composable pair and its composite have a common target. -/
theorem targetComparisonInvCondition {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback.fst G.s G.t ≫ G.t = G.c ≫ G.t := sorry

/-- The inverse comparison sends a composable pair to its first arrow and its composite. -/
def targetComparisonInv {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback G.s G.t ⟶ pullback G.t G.t :=
  pullback.lift (pullback.fst G.s G.t) G.c (targetComparisonInvCondition G)

/-- The first projection of the inverse comparison is the first arrow. -/
theorem targetComparisonInv_fst {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.targetComparisonInv ≫ pullback.fst G.t G.t = pullback.fst G.s G.t := sorry

/-- The second projection of the inverse comparison is composition. -/
theorem targetComparisonInv_snd {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.targetComparisonInv ≫ pullback.snd G.t G.t = G.c := sorry

/-- The target comparison followed by its inverse is the identity. -/
theorem targetComparison_hom_inv {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.targetComparison ≫ G.targetComparisonInv = 𝟙 (pullback G.t G.t) := sorry

/-- The inverse comparison followed by the target comparison is the identity. -/
theorem targetComparison_inv_hom {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.targetComparisonInv ≫ G.targetComparison = 𝟙 (pullback G.s G.t) := sorry

/-- The canonical isomorphism from common-target pairs to composable pairs. -/
def targetComparisonIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback G.t G.t ≅ pullback G.s G.t where
  hom := G.targetComparison
  inv := G.targetComparisonInv
  hom_inv_id := targetComparison_hom_inv G
  inv_hom_id := targetComparison_inv_hom G

/-- The forward map of `targetComparisonIso` is `(pr₀, c ∘ (i, 1))`. -/
theorem targetComparisonIso_hom {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.targetComparisonIso.hom = G.targetComparison := sorry

/-- The inverse map of `targetComparisonIso` is `(pr₀, c)`. -/
theorem targetComparisonIso_inv {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.targetComparisonIso.inv = G.targetComparisonInv := sorry

/-- The two projections from the scheme of composable arrows form a pullback square with the
source and target maps. -/
theorem fstSndIsPullback {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsPullback (pullback.fst G.s G.t) (pullback.snd G.s G.t) G.s G.t := sorry

/-- Composition and the second projection form a pullback square over the source map. -/
theorem compSndIsPullback {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsPullback G.c (pullback.snd G.s G.t) G.s G.s := sorry

/-- The first projection and composition form a pullback square over the target map. -/
theorem fstCompIsPullback {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsPullback (pullback.fst G.s G.t) G.c G.t G.t := sorry

end AlgebraicGeometry.GroupoidScheme
