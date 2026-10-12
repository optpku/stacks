/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Approximation

universe u

/- Lemma 29.46.11 (1): a universal homeomorphism of affine spectra is a filtered colimit of
finitely presented affine universal homeomorphisms. -/
@[stacks 0EUJ] #check
  (AlgebraicGeometry.UniversalHomeomorphism.finitePresentationOver_isFilteredColimit :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B],
      AlgebraicGeometry.UniversalHomeomorphism
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B))) →
        CategoryTheory.IsFiltered
            (AlgebraicGeometry.UniversalHomeomorphism.finitePresentationOverProperty
              (A := A) (B := B)).FullSubcategory ∧
          Nonempty (CategoryTheory.Limits.IsColimit
            (CategoryTheory.ObjectProperty.Over.forgetCocone
              (AlgebraicGeometry.UniversalHomeomorphism.finitePresentationOverProperty
                (A := A) (B := B)))))

/- Lemma 29.46.11 (2): if the affine universal homeomorphism also induces residue-field
isomorphisms, it is a filtered colimit of finitely presented morphisms with both properties. -/
@[stacks 0EUJ] #check
  (AlgebraicGeometry.UniversalHomeomorphism.finitePresentationResidueFieldIsoOver_isFilteredColimit :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B],
      AlgebraicGeometry.UniversalHomeomorphism
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B))) →
        (∀ x : AlgebraicGeometry.Spec (CommRingCat.of B),
          CategoryTheory.IsIso
            ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B))).residueFieldMap
              x)) →
          CategoryTheory.IsFiltered
              (AlgebraicGeometry.UniversalHomeomorphism.finitePresentationResidueFieldIsoOverProperty
                  (A := A) (B := B)).FullSubcategory ∧
            Nonempty (CategoryTheory.Limits.IsColimit
              (CategoryTheory.ObjectProperty.Over.forgetCocone
                (AlgebraicGeometry.UniversalHomeomorphism.finitePresentationResidueFieldIsoOverProperty
                    (A := A) (B := B)))))
