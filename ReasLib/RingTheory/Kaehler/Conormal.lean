/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.Kaehler
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Conormal maps of formally smooth quotients

This leaf records the presentation-independent consequence of formal
smoothness for a surjective algebra map: its conormal-to-Kaehler map splits.
The source algebra need not itself be formally smooth.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace KaehlerDifferential.Conormal

variable {R : Type u} {P : Type v} {S : Type w}
variable [CommRing R] [CommRing P] [CommRing S]
variable [Algebra R P] [Algebra R S] [Algebra P S] [IsScalarTower R P S]

/-- Lemma 10.131.10, tag `02HP`: an `R`-algebra section of a surjective presentation gives a
linear retraction of its canonical conormal map. -/
@[stacks 02HP "split conormal map of an algebra section"]
theorem has_retraction_of_section
    (sectionMap : S →ₐ[R] P)
    (hsection : (IsScalarTower.toAlgHom R P S).comp sectionMap = AlgHom.id R S) :
    ∃ retraction : S ⊗[P] Ω[P⁄R] →ₗ[P] (RingHom.ker (algebraMap P S)).Cotangent,
      retraction.comp (kerCotangentToTensor R P S) = LinearMap.id := by
  have hPS : Function.Surjective (algebraMap P S) := by
    intro s
    refine ⟨sectionMap s, ?_⟩
    simpa using AlgHom.congr_fun hsection s
  let sectionSquare : S →ₐ[R] P ⧸ RingHom.ker (algebraMap P S) ^ 2 :=
    (Ideal.Quotient.mkₐ R _).comp sectionMap
  have hsectionSquare :
      (IsScalarTower.toAlgHom R P S).kerSquareLift.comp sectionSquare =
        AlgHom.id R S := by
    ext s
    change algebraMap P S (sectionMap s) = s
    simpa using AlgHom.congr_fun hsection s
  let retraction :=
    (retractionKerCotangentToTensorEquivSection (R := R) hPS).symm
      ⟨sectionSquare, hsectionSquare⟩
  exact ⟨retraction.1, retraction.2⟩

/-- Tag `00TU`: for a surjective presentation of a formally smooth algebra,
the conormal map admits a linear retraction. -/
@[stacks 00TU "formally smooth conormal retraction"]
theorem has_retraction_of_formallySmooth
    [Algebra.FormallySmooth R S]
    (hPS : Function.Surjective (algebraMap P S)) :
    ∃ l : S ⊗[P] Ω[P⁄R] →ₗ[P] (RingHom.ker (algebraMap P S)).Cotangent,
      l.comp (kerCotangentToTensor R P S) = LinearMap.id := by
  let f := IsScalarTower.toAlgHom R P S
  have hkerSquareLift : Function.Surjective f.kerSquareLift :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hPS
  have hkerSquare : RingHom.ker f.kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  have hnilpotent : IsNilpotent (RingHom.ker f.kerSquareLift.toRingHom) :=
    ⟨2, hkerSquare⟩
  let sectionSquare : S →ₐ[R] P ⧸ RingHom.ker (algebraMap P S) ^ 2 :=
    Algebra.FormallySmooth.liftOfSurjective
      (AlgHom.id R S) f.kerSquareLift hkerSquareLift hnilpotent
  have hsectionSquare : f.kerSquareLift.comp sectionSquare = AlgHom.id R S := by
    exact Algebra.FormallySmooth.comp_liftOfSurjective
      (AlgHom.id R S) f.kerSquareLift hkerSquareLift hnilpotent
  let retraction :=
    (retractionKerCotangentToTensorEquivSection (R := R) hPS).symm
      ⟨sectionSquare, hsectionSquare⟩
  exact ⟨retraction.1, retraction.2⟩

/-- Tag `00TU`: the conormal map of a surjective presentation of a formally
smooth algebra is injective. -/
@[stacks 00TU "formally smooth conormal injectivity"]
theorem injective_of_formallySmooth
    [Algebra.FormallySmooth R S]
    (hPS : Function.Surjective (algebraMap P S)) :
    Function.Injective (kerCotangentToTensor R P S) := by
  obtain ⟨l, hl⟩ :=
    has_retraction_of_formallySmooth (R := R) (P := P) (S := S) hPS
  intro x y hxy
  have h := congr_arg l hxy
  simpa [← LinearMap.comp_apply, hl] using h

end KaehlerDifferential.Conormal
