/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Factorisation
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Coproduct.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.RelativeNormalization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Seminormalization

/-!
# Weak normalization in the normalization

This module describes weak normalizations as factorizations of normalization morphisms and
identifies the absolute weak normalization by its relative universal property.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A weak normalization of a scheme is an initial factorization of its normalization morphism
whose map to the scheme is a universal homeomorphism. -/
abbrev WeakNormalization (X : Scheme.{u})
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)] : Type (u + 1)
    :=
  { F : Scheme.Hom.RelativeWeakNormalizationFactorizations X.normalizationTo //
    Nonempty (IsInitial F) }

namespace WeakNormalization

variable {X : Scheme.{u}}
variable [QuasiCompact (genericPointSpectrumCoproductTo X)]
variable [QuasiSeparated (genericPointSpectrumCoproductTo X)]

/-- The intermediate scheme in a weak-normalization factorization. -/
def obj (W : WeakNormalization X) : Scheme.{u} :=
  W.1.1.mid

/-- The universal homeomorphism from a weak normalization to the original scheme. -/
def toScheme (W : WeakNormalization X) : W.obj ⟶ X :=
  W.1.1.π

/-- The morphism from the normalization to a weak normalization. -/
def fromNormalization (W : WeakNormalization X) : X.normalization ⟶ W.obj :=
  W.1.1.ι

/-- The normalization morphism is the composite through a weak normalization. -/
theorem fromNormalization_comp_toScheme (W : WeakNormalization X) :
    W.fromNormalization ≫ W.toScheme = X.normalizationTo :=
  W.1.1.ι_π

/-- The morphism from a weak normalization to the original scheme is a universal
homeomorphism. -/
theorem isUniversalHomeomorphism_toScheme (W : WeakNormalization X) :
    UniversalHomeomorphism W.toScheme :=
  Scheme.Hom.RelativeWeakNormalizationFactorizations.property W.1

/-- A weak normalization is initial among relative weak-normalization factorizations. -/
theorem nonempty_isInitial (W : WeakNormalization X) : Nonempty (IsInitial W.1) :=
  W.2

end WeakNormalization

namespace AbsoluteWeakNormalizationOver

/-- For a scheme with finitely many irreducible components on every compact open, its absolute
weak normalization is initial among factorizations of its normalization morphism through a
universal homeomorphism. -/
theorem initial_isRelativeOfNormalization
    (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    ∃ ι : X.normalization ⟶ (⊥_ (AbsoluteWeakNormalizationOver X)).1.left,
      ι ≫ (⊥_ (AbsoluteWeakNormalizationOver X)).1.hom = X.normalizationTo ∧
        ∀ {Z : Scheme.{u}} (g : X.normalization ⟶ Z) (π : Z ⟶ X),
          UniversalHomeomorphism π →
          g ≫ π = X.normalizationTo →
          ∃! h : (⊥_ (AbsoluteWeakNormalizationOver X)).1.left ⟶ Z,
            h ≫ π = (⊥_ (AbsoluteWeakNormalizationOver X)).1.hom ∧ ι ≫ h = g := sorry

end AbsoluteWeakNormalizationOver

end AlgebraicGeometry.Scheme
