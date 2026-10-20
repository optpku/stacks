module

public import ReasLib.AlgebraicGeometry.Scheme.Regular
import StacksCheckRecall

/-!
# Definition 28.9.1

A scheme is regular if its points admit affine open neighborhoods whose rings of sections are
Noetherian regular rings.

@stack 02IS
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

/- Definition 28.9.1

A scheme is regular, or nonsingular, if every point admits an affine open neighborhood whose ring
of sections is Noetherian and regular.
-/
@[stacks 02IS] #check
  (AlgebraicGeometry.Scheme.Regular : AlgebraicGeometry.Scheme.{u} → Prop)

#check
  (AlgebraicGeometry.Scheme.regular_iff :
    (X : AlgebraicGeometry.Scheme.{u}) →
      AlgebraicGeometry.Scheme.Regular X ↔
        ∀ x : X, ∃ U : X.affineOpens,
          x ∈ (U : X.Opens) ∧ IsRegularRing (Γ(X, (U : X.Opens))))

#check
  (AlgebraicGeometry.Scheme.exists_affineOpen_regularRing :
    (X : AlgebraicGeometry.Scheme.{u}) → [AlgebraicGeometry.Scheme.Regular X] →
      (x : X) → ∃ U : X.affineOpens,
        x ∈ (U : X.Opens) ∧ IsRegularRing (Γ(X, (U : X.Opens))))

#check
  (AlgebraicGeometry.Scheme.instIsLocallyNoetherianOfRegular :
    (X : AlgebraicGeometry.Scheme.{u}) → [AlgebraicGeometry.Scheme.Regular X] →
      AlgebraicGeometry.IsLocallyNoetherian X)

#check
  (AlgebraicGeometry.Scheme.isRegularLocalRing_stalk :
    (X : AlgebraicGeometry.Scheme.{u}) → [AlgebraicGeometry.Scheme.Regular X] →
      (x : X) → IsRegularLocalRing (X.presheaf.stalk x))
