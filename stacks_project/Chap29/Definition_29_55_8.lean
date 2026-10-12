/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.WeakNormalization.Normalization
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Definition 29.55.8

Let `X` be a scheme such that every quasi-compact open has finitely many irreducible components.
The weak normalization of `X` is the weak normalization of `X` in its normalization.
-/
@[stacks 0H3R] #check
  (AlgebraicGeometry.Scheme.AbsoluteWeakNormalizationOver.initial_isRelativeOfNormalization :
    ∀ (X : Scheme.{u}) [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X],
      ∃ ι : X.normalization ⟶ (⊥_ (Scheme.AbsoluteWeakNormalizationOver X)).1.left,
        ι ≫ (⊥_ (Scheme.AbsoluteWeakNormalizationOver X)).1.hom = X.normalizationTo ∧
          ∀ {Z : Scheme.{u}} (g : X.normalization ⟶ Z) (π : Z ⟶ X),
            UniversalHomeomorphism π →
            g ≫ π = X.normalizationTo →
            ∃! h : (⊥_ (Scheme.AbsoluteWeakNormalizationOver X)).1.left ⟶ Z,
              h ≫ π = (⊥_ (Scheme.AbsoluteWeakNormalizationOver X)).1.hom ∧ ι ≫ h = g)
