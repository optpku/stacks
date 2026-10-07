module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Coproduct.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Seminormalization

/-!
# Seminormalization in the normalization

This module identifies the absolute seminormalization by its relative universal property with
respect to the canonical normalization morphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- For a scheme with finitely many irreducible components on every compact open, its absolute
seminormalization is initial among factorizations of its normalization morphism through a
universal homeomorphism inducing isomorphisms on residue fields. -/
theorem initialSeminormalizationOver_isRelativeSeminormalizationOfNormalization
    (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    ∃ ι : X.normalization ⟶ (⊥_ (SeminormalizationOver X)).1.left,
      ι ≫ (⊥_ (SeminormalizationOver X)).1.hom = X.normalizationTo ∧
        ∀ {Z : Scheme.{u}} (g : X.normalization ⟶ Z) (π : Z ⟶ X),
          UniversalHomeomorphism π →
          (∀ z : Z, IsIso (Scheme.Hom.residueFieldMap π z)) →
          g ≫ π = X.normalizationTo →
          ∃! h : (⊥_ (SeminormalizationOver X)).1.left ⟶ Z,
            h ≫ π = (⊥_ (SeminormalizationOver X)).1.hom ∧ ι ≫ h = g := sorry

end AlgebraicGeometry.Scheme
