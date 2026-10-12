/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Completion.CoefficientField
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.RegularLocalRing.Parameters

@[expose] public section

/-!
# Power-Series Presentations of Complete Regular Local Rings

The two theorem owners in this leaf retain the finite variable type as
`MvPowerSeries σ _`; a `Fin d` presentation is only a consumer-side reindexing.

@stack 0C0S
@stack 0C35
-/

universe u v

open IsLocalRing

namespace IsRegularLocalRing

namespace MvPowerSeries

/-- Lemma 10.160.10 (1), tag `0C0S`: in equal characteristic, a complete
regular local ring is a formal power-series ring over its residue field. -/
@[stacks 0C0S "equal-characteristic complete regular local ring presentation"]
theorem exists_residueField_ringEquiv_of_ringChar_eq
    {R : Type u} [CommRing R] [IsCompleteLocalRing R]
    [IsRegularLocalRing R] (h : ringChar R = ringChar (ResidueField R)) :
    ∃ (σ : Type) (_ : Finite σ), Nonempty (MvPowerSeries σ (ResidueField R) ≃+* R) := sorry

/-- Lemma 10.160.10 (2), tag `0C0S`: a coefficient field mapping bijectively
to the residue field presents a complete regular local ring as a finite-variable
formal power-series algebra. -/
@[stacks 0C0S "coefficient-field presentation of a complete regular local ring"]
theorem exists_algEquiv_of_residueField_bijective
    {R : Type u} [CommRing R] [IsCompleteLocalRing R]
    [IsRegularLocalRing R] {k : Type v} [Field k] [Algebra k R]
    (h : Function.Bijective (ResidueField.map (algebraMap k R))) :
    ∃ (σ : Type) (_ : Finite σ), Nonempty (MvPowerSeries σ k ≃ₐ[k] R) := sorry

end MvPowerSeries

end IsRegularLocalRing

/-- Lemma 15.38.4 (Stacks `0C35`): a complete regular local `k`-algebra with separable
residue-field extension is a finite-variable formal power-series algebra over its residue
field. -/
@[stacks 0C35 "power-series presentation over a separable residue field"]
theorem exists_algEquiv_mvPowerSeries_residueField_of_isSeparableOver_of_isRegularLocalRing
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
    [IsCompleteLocalRing A] [IsRegularLocalRing A]
    [Algebra.IsSeparableOver k (ResidueField A)] :
    ∃ d : ℕ, Nonempty (MvPowerSeries (Fin d) (ResidueField A) ≃ₐ[k] A) := sorry
