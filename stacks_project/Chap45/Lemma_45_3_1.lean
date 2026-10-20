module

public import ReasLib.AlgebraicGeometry.Correspondence.Chow
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry TensorProduct

universe u

namespace AlgebraicGeometry.Correspondence

variable {k : Type u} [Field k]

/- Lemma 45.3.1 (1): composition of rational Chow correspondences is ℚ-linear
in the first correspondence. -/
@[stacks 0FG0] #check (AlgebraicGeometry.Correspondence.composition_linear_left :
  {X Y Z : SchemeOverField k} → [Smooth X.hom] → [Projective X.hom] →
  [Smooth Y.hom] → [Projective Y.hom] → [Smooth Z.hom] → [Projective Z.hom] →
  {r s : ℤ} → (a b : ℚ) → (c₁ c₂ : Rational X Y r) → (d : Rational Y Z s) →
  composition X Y Z r s (a • c₁ + b • c₂) d =
    a • composition X Y Z r s c₁ d + b • composition X Y Z r s c₂ d)

/- Lemma 45.3.1 (2): composition of rational Chow correspondences is ℚ-linear
in the second correspondence. -/
@[stacks 0FG0] #check (AlgebraicGeometry.Correspondence.composition_linear_right :
  {X Y Z : SchemeOverField k} → [Smooth X.hom] → [Projective X.hom] →
  [Smooth Y.hom] → [Projective Y.hom] → [Smooth Z.hom] → [Projective Z.hom] →
  {r s : ℤ} → (a b : ℚ) → (c : Rational X Y r) → (d₁ d₂ : Rational Y Z s) →
  composition X Y Z r s c (a • d₁ + b • d₂) =
    a • composition X Y Z r s c d₁ + b • composition X Y Z r s c d₂)

/- Lemma 45.3.1 (3): composition of rational Chow correspondences is associative
after canonical transport of the grading. -/
@[stacks 0FG0] #check (AlgebraicGeometry.Correspondence.composition_assoc :
  {X Y Z W : SchemeOverField k} → [Smooth X.hom] → [Projective X.hom] →
  [Smooth Y.hom] → [Projective Y.hom] → [Smooth Z.hom] → [Projective Z.hom] →
  [Smooth W.hom] → [Projective W.hom] → {r s t : ℤ} →
  (c : Rational X Y r) → (d : Rational Y Z s) → (e : Rational Z W t) →
  castDegree (add_assoc r s t)
      (composition X Z W (r + s) t (composition X Y Z r s c d) e) =
    composition X Y W r (s + t) c (composition Y Z W s t d e))

/- Lemma 45.3.1 (4): the canonical identification
CH_(-r)(X) ⊗ ℚ ≃ₗ[ℚ] Corr^r(X, Spec k). -/
@[stacks 0FG0] #check (AlgebraicGeometry.Correspondence.homologyEquiv :
  (X : SchemeOverField k) → [Smooth X.hom] → [Projective X.hom] → (r : ℤ) →
  RationalChowHomology X (-r) ≃ₗ[ℚ] Rational X (SchemeOverField.point k) r)

/- Lemma 45.3.1 (5): under the homological identification, pullback by a
correspondence is composition. -/
@[stacks 0FG0] #check (AlgebraicGeometry.Correspondence.homologyEquiv_pullback :
  {X Y : SchemeOverField k} → [Smooth X.hom] → [Projective X.hom] →
  [Smooth Y.hom] → [Projective Y.hom] → {r s : ℤ} →
  (c : Rational X Y r) → (alpha : RationalChowHomology Y (-s)) →
  homologyEquiv X (r + s) (pullback X Y r s c alpha) =
    composition X Y (SchemeOverField.point k) r s c (homologyEquiv Y s alpha))

/- Lemma 45.3.1 (6): the canonical identification
CH^r(X) ⊗ ℚ ≃ₗ[ℚ] Corr^r(Spec k, X). -/
@[stacks 0FG0] #check (AlgebraicGeometry.Correspondence.cohomologyEquiv :
  (X : SchemeOverField k) → [Smooth X.hom] → [Projective X.hom] → (r : ℤ) →
  RationalChowCohomology X r ≃ₗ[ℚ] Rational (SchemeOverField.point k) X r)

/- Lemma 45.3.1 (7): under the cohomological identification, pushforward by a
correspondence is composition. -/
@[stacks 0FG0] #check (AlgebraicGeometry.Correspondence.cohomologyEquiv_pushforward :
  {X Y : SchemeOverField k} → [Smooth X.hom] → [Projective X.hom] →
  [Smooth Y.hom] → [Projective Y.hom] → {r s : ℤ} →
  (c : Rational X Y r) → (alpha : RationalChowCohomology X s) →
  cohomologyEquiv Y (s + r) (pushforward X Y r s c alpha) =
    composition (SchemeOverField.point k) X Y s r (cohomologyEquiv X s alpha) c)

/- Lemma 45.3.1 (8): pullback of rational Chow cycles is compatible with
composition of correspondences. -/
@[stacks 0FG0] #check (AlgebraicGeometry.Correspondence.pullback_composition :
  {X Y Z : SchemeOverField k} → [Smooth X.hom] → [Projective X.hom] →
  [Smooth Y.hom] → [Projective Y.hom] → [Smooth Z.hom] → [Projective Z.hom] →
  {r s t : ℤ} → (c : Rational X Y r) → (d : Rational Y Z s) →
  (alpha : RationalChowHomology Z (-t)) →
  castHomologyDegree (congrArg Neg.neg (add_assoc r s t))
      (pullback X Z (r + s) t (composition X Y Z r s c d) alpha) =
    pullback X Y r (s + t) c (pullback Y Z s t d alpha))

/- Lemma 45.3.1 (9): pushforward of rational Chow cycles is compatible with
composition of correspondences. -/
@[stacks 0FG0] #check (AlgebraicGeometry.Correspondence.pushforward_composition :
  {X Y Z : SchemeOverField k} → [Smooth X.hom] → [Projective X.hom] →
  [Smooth Y.hom] → [Projective Y.hom] → [Smooth Z.hom] → [Projective Z.hom] →
  {r s t : ℤ} → (c : Rational X Y r) → (d : Rational Y Z s) →
  (alpha : RationalChowCohomology X t) →
  castCohomologyDegree (add_assoc t r s).symm
      (pushforward X Z (r + s) t (composition X Y Z r s c d) alpha) =
    pushforward Y Z s (t + r) d (pushforward X Y r t c alpha))

end AlgebraicGeometry.Correspondence
