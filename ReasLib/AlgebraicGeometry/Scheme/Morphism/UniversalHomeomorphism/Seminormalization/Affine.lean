module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Affine seminormalization

This module records the maximal intermediate subalgebra characterized by a universal
homeomorphism on spectra and isomorphisms on residue fields.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.UniversalHomeomorphism

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- An intermediate subalgebra is a maximal seminormalization when its spectrum is universally
homeomorphic to the base with unchanged residue fields, and it contains every compatible
intermediate algebra with the same properties. -/
def IsMaximalSeminormalizationSubalgebra (B' : Subalgebra A B) : Prop :=
  AlgebraicGeometry.UniversalHomeomorphism
      (Spec.map (CommRingCat.ofHom (algebraMap A B'))) ∧
    (∀ x : Spec (CommRingCat.of B'),
      IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A B'))).residueFieldMap x)) ∧
      ∀ {C : Type u} [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B],
        AlgebraicGeometry.UniversalHomeomorphism
            (Spec.map (CommRingCat.ofHom (algebraMap A C))) →
          (∀ x : Spec (CommRingCat.of C),
            IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A C))).residueFieldMap x)) →
            ∀ c : C, algebraMap C B c ∈ B'

/-- The maximal seminormalization predicate is exactly the conjunction of the spectrum,
residue-field, and universal containment conditions. -/
theorem isMaximalSeminormalizationSubalgebra_iff (B' : Subalgebra A B) :
    IsMaximalSeminormalizationSubalgebra B' ↔
      AlgebraicGeometry.UniversalHomeomorphism
          (Spec.map (CommRingCat.ofHom (algebraMap A B'))) ∧
        (∀ x : Spec (CommRingCat.of B'),
          IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A B'))).residueFieldMap x)) ∧
          ∀ {C : Type u} [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B],
            AlgebraicGeometry.UniversalHomeomorphism
                (Spec.map (CommRingCat.ofHom (algebraMap A C))) →
              (∀ x : Spec (CommRingCat.of C),
                IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A C))).residueFieldMap x)) →
                ∀ c : C, algebraMap C B c ∈ B' := Iff.rfl

/-- A dominant affine spectrum map admits a maximal intermediate seminormalization subalgebra. -/
@[stacks 0H3L]
theorem exists_maximalSeminormalizationSubalgebra_of_isDominantSpecMap
    (hAB : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    ∃ B' : Subalgebra A B, IsMaximalSeminormalizationSubalgebra B' := sorry

end AlgebraicGeometry.UniversalHomeomorphism
