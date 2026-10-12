/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism
public import ReasLib.CategoryTheory.ObjectProperty.Over.Basic

/-!
# Finite-presentation approximation of affine universal homeomorphisms

This module records filtered-colimit presentations of affine universal homeomorphisms by
finitely presented algebras, with an optional residue-field isomorphism condition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.UniversalHomeomorphism

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The property of an `A`-algebra over `B` being finitely presented over `A` and inducing a
universal homeomorphism on spectra. -/
abbrev finitePresentationOverProperty : ObjectProperty (Over (CommAlgCat.of A B)) := fun C ↦
  Algebra.FinitePresentation A C.left ∧
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A C.left)))

/-- The property of an `A`-algebra over `B` being finitely presented over `A`, inducing a
universal homeomorphism on spectra, and inducing isomorphisms on residue fields. -/
abbrev finitePresentationResidueFieldIsoOverProperty :
    ObjectProperty (Over (CommAlgCat.of A B)) := fun C ↦
  Algebra.FinitePresentation A C.left ∧
    (let f : Spec (CommRingCat.of C.left) ⟶ Spec (CommRingCat.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A C.left))
    UniversalHomeomorphism f ∧
      ∀ x : Spec (CommRingCat.of C.left), IsIso (f.residueFieldMap x))

/-- Finitely presented `A`-algebras over `B` inducing universal homeomorphisms on spectra form
a filtered category whose canonical cocone has colimit `B`, provided `A → B` itself induces a
universal homeomorphism. -/
theorem finitePresentationOver_isFilteredColimit
    (hAB : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    IsFiltered (finitePresentationOverProperty (A := A) (B := B)).FullSubcategory ∧
      Nonempty (IsColimit (CategoryTheory.ObjectProperty.Over.forgetCocone
        (finitePresentationOverProperty (A := A) (B := B)))) := sorry

/-- Finitely presented `A`-algebras over `B` inducing universal homeomorphisms and residue-field
isomorphisms form a filtered category whose canonical cocone has colimit `B`, provided `A → B`
has both properties. -/
theorem finitePresentationResidueFieldIsoOver_isFilteredColimit
    (hAB : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hκ : ∀ x : Spec (CommRingCat.of B),
      IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A B))).residueFieldMap x)) :
    IsFiltered
        (finitePresentationResidueFieldIsoOverProperty (A := A) (B := B)).FullSubcategory ∧
      Nonempty (IsColimit (CategoryTheory.ObjectProperty.Over.forgetCocone
        (finitePresentationResidueFieldIsoOverProperty (A := A) (B := B)))) := sorry

end AlgebraicGeometry.UniversalHomeomorphism
