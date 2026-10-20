module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Seminormalization
public import ReasLib.RingTheory.Frobenius.Colimit

/-!
# Frobenius colimits and absolute weak normalization

This module presents the Frobenius colimit of a commutative `ZMod p`-algebra as an
absolute weak normalization candidate and records its terminal comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Ring.FrobeniusColimit

/-- The initial-stage map into a Frobenius colimit induces a universal homeomorphism
on affine spectra. -/
theorem spectrumMap_universalHomeomorphism (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] :
    AlgebraicGeometry.UniversalHomeomorphism
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A (ring p A)))) := sorry

/-- The Frobenius colimit as an `A`-algebra presenting an absolute weak normalization
candidate. -/
noncomputable def asAbsoluteWeakNormalizationAlgebra (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] :
    AlgebraicGeometry.AbsoluteWeakNormalizationAlgebras A :=
  ⟨CommAlgCat.of A (ring p A), spectrumMap_universalHomeomorphism p A⟩

/-- The underlying commutative algebra of the absolute weak normalization candidate is
the Frobenius colimit with its canonical `A`-algebra structure. -/
theorem asAbsoluteWeakNormalizationAlgebra_obj (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] :
    (asAbsoluteWeakNormalizationAlgebra p A).1 = CommAlgCat.of A (ring p A) := sorry

/-- The canonical comparison from the Frobenius colimit to the terminal absolute weak
normalization is an isomorphism. -/
@[instance]
theorem instIsIsoToAbsoluteWeakNormalization (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] :
    IsIso
      (terminal.from (asAbsoluteWeakNormalizationAlgebra p A) :
        asAbsoluteWeakNormalizationAlgebra p A ⟶
          ⊤_ (AlgebraicGeometry.AbsoluteWeakNormalizationAlgebras A)) := sorry

end Ring.FrobeniusColimit
