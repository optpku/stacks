/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import Mathlib.RingTheory.QuasiFinite.Basic
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.RingHom
public import ReasLib.RingTheory.MvPolynomial.TensorEquivSum
import Mathlib.Tactic.CrossRefAttribute

/-!
# Generic Factorization in Sum-Indexed Polynomial Rings

@stack 00SQ
-/

@[expose] public section

open Polynomial
open scoped TensorProduct

noncomputable section

universe u

namespace MvPolynomial.SumFactorization

variable (R : Type u) [CommRing R] (m k : ℕ)

/-- The generic factorization map, expressed with a sum-indexed target. -/
@[stacks 00SQ "sum-indexed generic factorization map"]
noncomputable def map :
    MvPolynomial (Fin (m + k)) R →ₐ[R] MvPolynomial (Fin m ⊕ Fin k) R :=
  (MvPolynomial.tensorEquivSum R (Fin m) (Fin k) R).toAlgHom.comp
    (MvPolynomial.universalFactorizationMap R (m + k) m k rfl)

/-- The underlying ring homomorphism is the canonical factorization map followed by
the sum-variable equivalence. -/
@[simp, stacks 00SQ "underlying generic factorization ring homomorphism"]
theorem map_toRingHom :
    (map R m k).toRingHom =
      (MvPolynomial.tensorEquivSum R (Fin m) (Fin k) R).toRingHom.comp
        (MvPolynomial.universalFactorizationMap R (m + k) m k rfl).toRingHom :=
  rfl

/-- The generic monic polynomial maps to the product of its two generic factors. -/
@[stacks 00SQ "generic monic factorization identity"]
theorem map_freeMonic :
    (freeMonic R (m + k)).map (map R m k) =
      ((freeMonic R m).map (MvPolynomial.rename Sum.inl).toRingHom) *
        ((freeMonic R k).map (MvPolynomial.rename Sum.inr).toRingHom) := by
  have htransport := congrArg
    (Polynomial.map (MvPolynomial.tensorEquivSum R (Fin m) (Fin k) R).toRingHom)
    (MvPolynomial.universalFactorizationMap_freeMonic R (m + k) m k rfl)
  change Polynomial.map (map R m k).toRingHom (freeMonic R (m + k)) = _
  rw [map_toRingHom]
  simp only [Polynomial.map_mul, Polynomial.map_map,
    Algebra.TensorProduct.algebraMap_def, Algebra.algebraMap_self, RingHom.comp_id] at htransport
  rw [MvPolynomial.TensorEquivSum.comp_includeLeft,
    MvPolynomial.TensorEquivSum.comp_includeRight] at htransport
  exact htransport

/-- The generic factorization map is finite. -/
@[stacks 00SQ "finite generic factorization map"]
theorem map_finite : (map R m k).Finite := by
  change (map R m k).toRingHom.Finite
  rw [map_toRingHom]
  exact RingHom.Finite.comp
    (RingEquiv.finite (MvPolynomial.tensorEquivSum R (Fin m) (Fin k) R).toRingEquiv)
    (MvPolynomial.finite_universalFactorizationMap R (m + k) m k rfl)

/-- Every nonempty fiber of the generic factorization map is zero-dimensional. -/
@[stacks 00SQ "zero-dimensional nonempty fibers"]
theorem fiber_ringKrullDim_eq_zero :
    letI := (map R m k).toAlgebra
    ∀ p : PrimeSpectrum (MvPolynomial (Fin (m + k)) R),
      Nonempty (PrimeSpectrum (p.asIdeal.Fiber (MvPolynomial (Fin m ⊕ Fin k) R))) →
        ringKrullDim (p.asIdeal.Fiber (MvPolynomial (Fin m ⊕ Fin k) R)) = 0 := by
  letI := (map R m k).toAlgebra
  intro p hp
  letI : Module.Finite (MvPolynomial (Fin (m + k)) R)
      (MvPolynomial (Fin m ⊕ Fin k) R) :=
    (RingHom.finite_algebraMap).mp (map_finite R m k)
  letI : Module.Finite p.asIdeal.ResidueField
      (p.asIdeal.Fiber (MvPolynomial (Fin m ⊕ Fin k) R)) := inferInstance
  letI : Nontrivial (p.asIdeal.Fiber (MvPolynomial (Fin m ⊕ Fin k) R)) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp hp
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp <|
    (Module.finite_iff_krullDimLE_zero p.asIdeal.ResidueField
      (p.asIdeal.Fiber (MvPolynomial (Fin m ⊕ Fin k) R))).mp inferInstance

/-- The sum-indexed map has a relative global complete-intersection presentation. -/
@[stacks 00SQ "relative global complete-intersection presentation"]
theorem exists_presentation :
    letI := (map R m k).toAlgebra
    ∃ P : Algebra.Presentation (MvPolynomial (Fin (m + k)) R)
        (MvPolynomial (Fin m ⊕ Fin k) R) (Fin (m + k)) (Fin (m + k)),
      P.IsRelativeGlobalCompleteIntersection := by
  letI := (map R m k).toAlgebra
  letI := (MvPolynomial.universalFactorizationMap R (m + k) m k rfl).toAlgebra
  let P₀ : Algebra.Presentation (MvPolynomial (Fin (m + k)) R)
      (MvPolynomial (Fin m ⊕ Fin k) R) (Fin m ⊕ Fin k) (Fin (m + k)) :=
    ((MvPolynomial.universalFactorizationMapPresentation R (m + k) m k rfl).toPresentation).ofAlgEquiv
        { __ := MvPolynomial.tensorEquivSum R (Fin m) (Fin k) R
          commutes' := fun r ↦ rfl }
  let P : Algebra.Presentation (MvPolynomial (Fin (m + k)) R)
      (MvPolynomial (Fin m ⊕ Fin k) R) (Fin (m + k)) (Fin (m + k)) :=
    P₀.reindex (finSumFinEquiv.symm : Fin (m + k) ≃ Fin m ⊕ Fin k) (Equiv.refl _)
  have hdim : P.dimension = 0 := by
    calc
      P.dimension = P₀.dimension := by
        simp [P]
      _ =
          ((MvPolynomial.universalFactorizationMapPresentation R (m + k) m k rfl).toPresentation).dimension := by
        simp [P₀]
      _ = 0 := by
        simp [Algebra.Presentation.dimension]
  refine ⟨P, le_rfl, fun p hp ↦ ?_⟩
  have hfiber :
      ringKrullDim (p.asIdeal.Fiber (MvPolynomial (Fin m ⊕ Fin k) R)) = 0 :=
    fiber_ringKrullDim_eq_zero R m k p hp
  simpa [hdim] using hfiber

/-- The generic factorization map is a relative global complete intersection. -/
@[stacks 00SQ "relative global complete intersection"]
theorem isRelativeGlobalCompleteIntersection :
    (map R m k).toRingHom.IsRelativeGlobalCompleteIntersection := by
  change @Algebra.IsRelativeGlobalCompleteIntersection
    (MvPolynomial (Fin (m + k)) R) (MvPolynomial (Fin m ⊕ Fin k) R) _ _
      (map R m k).toAlgebra
  letI := (map R m k).toAlgebra
  obtain ⟨P, hP⟩ := exists_presentation R m k
  exact { exists_presentation := ⟨m + k, m + k, P, hP⟩ }

end MvPolynomial.SumFactorization
