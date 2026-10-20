/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.Algebraic.ResidueField
public import ReasLib.Algebra.WLocalIndEtale.Cover

/-!
# Relative w-local ind-étale lifts

The lift of `Cover A` along an algebra `A → B` inducing algebraic residue-field
extensions, obtained by specializing `B ⊗[A] Cover A` along the image of the
closed-points ideal of `Cover A`.
-/

@[expose] public section

universe u v

open Algebra.WLocalHull Algebra.IndEtaleEnvelope

namespace Algebra.WLocalIndEtale

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

/-- The relative w-local faithfully flat ind-étale lift of `Cover A` along
`A → B`. -/
noncomputable abbrev Over : Type (max u v) :=
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
  rfl

/-- `toOver` is the composite of `includeRight` with the structure map of
`alongClosed`. -/
theorem toOver_comp :
    toOver A B =
      (algebraMap (TensorProduct A B (Cover A)) (Over A B)).comp
        (Algebra.TensorProduct.includeRight : Cover A →ₐ[A]
          TensorProduct A B (Cover A)).toRingHom :=
  rfl

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

/-- The canonical square over an algebra inducing algebraic residue-field extensions
commutes, has faithfully flat ind-étale horizontal maps and w-local target spectra,
and induces a w-local map with exact closed-point preimage. Its closed points
surject onto both original spectra, and every maximal localization of the
absolute cover is strictly henselian. -/
theorem square_spec [Fact (IsAlgebraicOnResidueFields A B)] :
    (toOver A B).comp (algebraMap A (Cover A)) =
        (algebraMap B (Over A B)).comp (algebraMap A B) ∧
      (algebraMap A (Cover A)).FaithfullyFlat ∧
      (algebraMap A (Cover A)).IndEtale ∧
      (algebraMap B (Over A B)).FaithfullyFlat ∧
      (algebraMap B (Over A B)).IndEtale ∧
      WLocalSpace (PrimeSpectrum (Cover A)) ∧
      WLocalSpace (PrimeSpectrum (Over A B)) ∧
      IsWLocalMap (PrimeSpectrum.comap (toOver A B)) ∧
      PrimeSpectrum.comap (toOver A B) ⁻¹'
          closedPoints (PrimeSpectrum (Cover A)) =
        closedPoints (PrimeSpectrum (Over A B)) ∧
      Set.SurjOn (PrimeSpectrum.comap (algebraMap A (Cover A)))
        (closedPoints (PrimeSpectrum (Cover A))) Set.univ ∧
      Set.SurjOn (PrimeSpectrum.comap (algebraMap B (Over A B)))
        (closedPoints (PrimeSpectrum (Over A B))) Set.univ ∧
      ∀ (m : Ideal (Cover A)) [m.IsMaximal],
        StrictHenselianLocalRing (Localization.AtPrime m) := by
  exact ⟨comm A B, algebraMap_faithfullyFlat A, indEtale A,
    algebraMap_faithfullyFlat_over A B Fact.out, indEtale_over A B Fact.out,
    instWLocalSpace A, instWLocalSpace_over A B, instIsWLocalMap A B,
    closedPoints_eq_preimage A B Fact.out, surjOn_closedPoints A,
    surjOn_closedPoints_over A B Fact.out,
    fun m _ => instStrictHenselianLocalRing A m⟩

end Algebra.WLocalIndEtale
