module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Seminormalization.Normalization

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 29.55.7

Let `X` be a scheme such that every quasi-compact open has finitely many irreducible components.
Then the seminormalization of `X` in its normalization is the seminormalization of `X`.
-/
@[stacks 0H3Q] #check
  (AlgebraicGeometry.Scheme.initialSeminormalizationOver_isRelativeSeminormalizationOfNormalization :
    ∀ (X : Scheme.{u}) [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X],
      ∃ ι : X.normalization ⟶ (⊥_ (Scheme.SeminormalizationOver X)).1.left,
        ι ≫ (⊥_ (Scheme.SeminormalizationOver X)).1.hom = X.normalizationTo ∧
          ∀ {Z : Scheme.{u}} (g : X.normalization ⟶ Z) (π : Z ⟶ X),
            UniversalHomeomorphism π →
            (∀ z : Z, IsIso (Scheme.Hom.residueFieldMap π z)) →
            g ≫ π = X.normalizationTo →
            ∃! h : (⊥_ (Scheme.SeminormalizationOver X)).1.left ⟶ Z,
              h ≫ π = (⊥_ (Scheme.SeminormalizationOver X)).1.hom ∧ ι ≫ h = g)
