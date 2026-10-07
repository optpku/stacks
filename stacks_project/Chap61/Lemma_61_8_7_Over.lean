module

import Mathlib.RingTheory.TensorProduct.Basic
public import stacks_project.Chap61.Lemma_61_5_6_ResidueField
public import stacks_project.Chap61.Lemma_61_8_7_Cover

/-!
# Relative w-local ind-étale lifts

The lift of `Cover A` along an algebra `A → B` inducing algebraic residue-field
extensions, obtained by specializing `B ⊗[A] Cover A` along the image of the
closed-points ideal of `Cover A`.
-/

@[expose] public section

universe u

open Algebra.WLocalHull Algebra.IndEtaleEnvelope

namespace Algebra.WLocalIndEtale

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The relative w-local faithfully flat ind-étale lift of `Cover A` along
`A → B`. -/
noncomputable abbrev Over : Type u :=
  alongClosed (TensorProduct A B (Cover A))
    ((closedPointsIdeal (Cover A)).map
      (Algebra.TensorProduct.includeRight : Cover A →ₐ[A]
        TensorProduct A B (Cover A)).toRingHom)

/-- The structure map `Cover A → Over A B` through `B ⊗[A] Cover A`. -/
noncomputable def toOver : Cover A →+* Over A B :=
  (algebraMap (TensorProduct A B (Cover A)) (Over A B)).comp
    (Algebra.TensorProduct.includeRight : Cover A →ₐ[A]
      TensorProduct A B (Cover A)).toRingHom

/-- The structure map `B → Over A B` through `B ⊗[A] Cover A`. -/
noncomputable instance instAlgebra_over : Algebra B (Over A B) :=
  RingHom.toAlgebra
    ((algebraMap (TensorProduct A B (Cover A)) (Over A B)).comp
      (Algebra.TensorProduct.includeLeftRingHom : B →+*
        TensorProduct A B (Cover A)))

/-- The `B`-algebra map of `Over A B` is the composite of `includeLeftRingHom`
with the structure map of `alongClosed`. -/
theorem algebraMap_over_eq :
    algebraMap B (Over A B) =
      (algebraMap (TensorProduct A B (Cover A)) (Over A B)).comp
        (Algebra.TensorProduct.includeLeftRingHom : B →+*
          TensorProduct A B (Cover A)) :=
  sorry

/-- `toOver` is the composite of `includeRight` with the structure map of
`alongClosed`. -/
theorem toOver_comp :
    toOver A B =
      (algebraMap (TensorProduct A B (Cover A)) (Over A B)).comp
        (Algebra.TensorProduct.includeRight : Cover A →ₐ[A]
          TensorProduct A B (Cover A)).toRingHom :=
  sorry

/-- The square `A → Cover A → Over A B` and `A → B → Over A B` commutes. -/
theorem comm :
    (toOver A B).comp (algebraMap A (Cover A)) =
      (algebraMap B (Over A B)).comp (algebraMap A B) :=
  sorry

/-- `Over A B` is faithfully flat as a `B`-algebra when residue-field extensions
of `A → B` are algebraic. -/
instance instFaithfullyFlat_over [Fact (IsAlgebraicOnResidueFields A B)] :
    Module.FaithfullyFlat B (Over A B) :=
  sorry

/-- The structure map `B → Over A B` is faithfully flat when residue-field
extensions of `A → B` are algebraic. -/
theorem algebraMap_faithfullyFlat_over (h : IsAlgebraicOnResidueFields A B) :
    (algebraMap B (Over A B)).FaithfullyFlat :=
  sorry

/-- The structure map `B → Over A B` is ind-étale when residue-field extensions
of `A → B` are algebraic. -/
theorem indEtale_over (h : IsAlgebraicOnResidueFields A B) :
    (algebraMap B (Over A B)).IndEtale :=
  sorry

/-- `PrimeSpectrum (Over A B)` is a w-local space when residue-field extensions
of `A → B` are algebraic. -/
instance instWLocalSpace_over [Fact (IsAlgebraicOnResidueFields A B)] :
    WLocalSpace (PrimeSpectrum (Over A B)) :=
  sorry

/-- `PrimeSpectrum.comap (toOver A B)` is a w-local map when residue-field
extensions of `A → B` are algebraic. -/
instance instIsWLocalMap [Fact (IsAlgebraicOnResidueFields A B)] :
    IsWLocalMap (PrimeSpectrum.comap (toOver A B)) :=
  sorry

/-- Closed points of `PrimeSpectrum (Over A B)` are the preimage of those of
`PrimeSpectrum (Cover A)`. -/
theorem closedPoints_eq_preimage (h : IsAlgebraicOnResidueFields A B) :
    PrimeSpectrum.comap (toOver A B) ⁻¹'
        closedPoints (PrimeSpectrum (Cover A)) =
      closedPoints (PrimeSpectrum (Over A B)) :=
  sorry

/-- Closed points of `PrimeSpectrum (Over A B)` surject onto `PrimeSpectrum B`. -/
theorem surjOn_closedPoints_over (h : IsAlgebraicOnResidueFields A B) :
    Set.SurjOn (PrimeSpectrum.comap (algebraMap B (Over A B)))
      (closedPoints (PrimeSpectrum (Over A B))) Set.univ :=
  sorry

end Algebra.WLocalIndEtale
