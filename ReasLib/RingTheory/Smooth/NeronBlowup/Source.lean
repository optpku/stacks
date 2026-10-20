/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.BaseChange
public import ReasLib.RingTheory.Smooth.NeronBlowup.Core

/-!
# Affine Neron blowups from source presentations

This file owns induced closed centers on source algebras and the comparison
between a base-changed source chart and the affine Neron blowup.
-/

@[expose] public section

noncomputable section

open Ideal IsLocalRing
open scoped AffineBlowupChart TensorProduct

universe u v x

namespace Algebra.DVR.Factorization

variable {R : Type u} {L : Type v}
variable [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [CommRing L] [IsDomain L] [IsDiscreteValuationRing L]
variable [Algebra R L]

/-- The closed center induced by a ring map into the intermediate algebra. -/
@[stacks 0BJ3 "source closed center"]
def sourceCenter
    (S : Algebra.DVR.Factorization R L) {B : Type x} [CommRing B]
    (g : B →+* S.mid) : Ideal B :=
  Ideal.comap g S.closedIdeal

namespace sourceCenter

/-- The closed center induced on a source algebra is prime. -/
@[stacks 0BJ3 "source center is prime"]
instance instIsPrime
    (S : Algebra.DVR.Factorization R L) {B : Type x} [CommRing B]
    (g : B →+* S.mid) :
    (S.sourceCenter g).IsPrime := sorry

/-- Lemma 16.4.2 (2) (Tag 0BJ3): a surjection carries its induced source
center onto the closed center of the DVR factorization. -/
@[stacks 0BJ3]
theorem map_eq
    (S : Algebra.DVR.Factorization R L) {B : Type x} [CommRing B]
    (g : B →+* S.mid) (h : Function.Surjective g) :
    Ideal.map g (S.sourceCenter g) = S.closedIdeal := sorry

end sourceCenter

/-- The prime-spectrum point defined by the closed center on a source algebra. -/
@[stacks 0BJ3 "source closed center point"]
abbrev sourceCenterPoint
    (S : Algebra.DVR.Factorization R L) {B : Type x} [CommRing B]
    (g : B →+* S.mid) : PrimeSpectrum B :=
  ⟨S.sourceCenter g, inferInstance⟩

/-- A uniformizer maps into the closed center on a source algebra. -/
theorem sourceParameter_mem
    [IsExtensionOfDiscreteValuationRings R L]
    (S : Algebra.DVR.Factorization R L) {B : Type x} [CommRing B]
    [Algebra R B] (g : B →ₐ[R] S.mid)
    (π : R) (hπ : Irreducible π) :
    algebraMap R B π ∈ S.sourceCenter g.toRingHom := sorry

/-- The image of a uniformizer in the closed center on a source algebra. -/
@[stacks 0BJ3 "source uniformizer"]
def sourceParameter
    [IsExtensionOfDiscreteValuationRings R L]
    (S : Algebra.DVR.Factorization R L) {B : Type x} [CommRing B]
    [Algebra R B] (g : B →ₐ[R] S.mid)
    (π : R) (hπ : Irreducible π) : S.sourceCenter g.toRingHom :=
  ⟨algebraMap R B π, S.sourceParameter_mem g π hπ⟩

namespace NeronBlowup.Source

variable (S : Algebra.DVR.Factorization R L) {B : Type x} [CommRing B]
variable [Algebra R B] [Algebra B S.mid] [IsScalarTower R B S.mid]

/-- The canonical map from a source algebra into the intermediate algebra of
a DVR factorization. -/
abbrev map : B →ₐ[R] S.mid :=
  IsScalarTower.toAlgHom R B S.mid

/-- The closed center induced on a source algebra. -/
abbrev center : Ideal B :=
  S.sourceCenter (map (B := B) S).toRingHom

/-- A surjection identifies the extended source center with the closed center
of the target DVR factorization. -/
@[stacks 0BJ3 "source center comparison"]
theorem center_eq (h : Function.Surjective (algebraMap B S.mid)) :
    Ideal.map (algebraMap B S.mid) (center (B := B) S) = S.closedIdeal := sorry

variable [IsExtensionOfDiscreteValuationRings R L]

/-- The image of a source uniformizer in the induced source center. -/
@[stacks 0BJ3 "source Neron parameter"]
def parameter (π : R) (hπ : Irreducible π) : center (B := B) S :=
  S.sourceParameter (map (B := B) S) π hπ

/-- The affine Neron chart formed on a source algebra. -/
@[stacks 0BJ3 "source Neron chart"]
abbrev Chart (π : R) (hπ : Irreducible π) :=
  affineBlowupChart (center (B := B) S) (parameter (B := B) S π hπ)

/-- The base change of a source Neron chart to the intermediate algebra. -/
@[stacks 0BIP "base-changed source Neron chart"]
abbrev Tensor (π : R) (hπ : Irreducible π) :=
  S.mid ⊗[B] Chart (B := B) S π hπ

/-- The base-changed source chart modulo uniformizer-power torsion. -/
@[stacks 0BIP "source Neron base-change quotient"]
abbrev Quotient (π : R) (hπ : Irreducible π) :=
  AffineBlowupChart.TensorQuotient S.mid (center (B := B) S)
    (parameter (B := B) S π hπ)

/-- The canonical comparison from a base-changed source chart directly to the affine Neron
blowup of the DVR factorization. -/
@[stacks 0BJ3 "source Neron comparison"]
noncomputable def comparison (π : R) (hπ : Irreducible π) :
    Tensor (B := B) S π hπ →ₐ[S.mid] S.NeronBlowup π hπ :=
  AffineBlowupChart.tensorMap S.mid (center (B := B) S) S.closedIdeal (hIJ := le_rfl)
    (parameter (B := B) S π hπ) (S.neronBlowupParameter π hπ)
    (hab := (IsScalarTower.algebraMap_apply R B S.mid π).symm)

/-- The canonical comparison from the source chart modulo uniformizer-power torsion directly to
the affine Neron blowup. -/
@[stacks 0BJ3 "source Neron quotient comparison"]
noncomputable def quotientComparison (π : R) (hπ : Irreducible π) :
    Quotient (B := B) S π hπ →ₐ[S.mid] S.NeronBlowup π hπ :=
  AffineBlowupChart.tensorQuotientMap S.mid (center (B := B) S) S.closedIdeal (hIJ := le_rfl)
    (parameter (B := B) S π hπ) (S.neronBlowupParameter π hπ)
    (hab := (IsScalarTower.algebraMap_apply R B S.mid π).symm)

namespace comparison

/-- For a surjective source presentation, the direct comparison to the affine Neron blowup is
surjective. -/
@[stacks 0BJ3 "source Neron comparison surjective"]
theorem surjective (π : R) (hπ : Irreducible π)
    (h : Function.Surjective (algebraMap B S.mid)) :
    Function.Surjective (Source.comparison (B := B) S π hπ) := sorry

/-- For a surjective source presentation, the kernel of the direct Neron comparison is the
uniformizer-power-torsion ideal. -/
@[stacks 0BJ3 "source Neron comparison kernel"]
theorem ker_eq_powerTorsion (π : R) (hπ : Irreducible π)
    (h : Function.Surjective (algebraMap B S.mid)) :
    RingHom.ker (Source.comparison (B := B) S π hπ).toRingHom =
      Ideal.principalPowerTorsion
        (algebraMap B (Tensor (B := B) S π hπ) (algebraMap R B π)) := sorry

/-- For a surjective source presentation, the kernel of the direct Neron comparison is exactly
the torsion killed by a power of the uniformizer. -/
@[stacks 0BJ3 "source Neron comparison kernel membership", simp]
theorem mem_ker_iff (π : R) (hπ : Irreducible π)
    (h : Function.Surjective (algebraMap B S.mid))
    (x : Tensor (B := B) S π hπ) :
    x ∈ RingHom.ker (Source.comparison (B := B) S π hπ).toRingHom ↔
      ∃ n : ℕ,
        (algebraMap B (Tensor (B := B) S π hπ) (algebraMap R B π)) ^ n * x = 0 :=
  sorry

end comparison

namespace quotientComparison

/-- For a surjective source presentation, quotienting by uniformizer-power torsion gives the
affine Neron blowup. -/
@[stacks 0BJ3 "source Neron quotient comparison bijective"]
theorem bijective (π : R) (hπ : Irreducible π)
    (h : Function.Surjective (algebraMap B S.mid)) :
    Function.Bijective (Source.quotientComparison (B := B) S π hπ) := sorry

end quotientComparison

end NeronBlowup.Source

end Algebra.DVR.Factorization
