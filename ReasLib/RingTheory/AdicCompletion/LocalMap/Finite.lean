/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import ReasLib.RingTheory.AdicCompletion.AlgebraMap
public import ReasLib.RingTheory.AdicCompletion.Cofinal
public import ReasLib.RingTheory.AdicCompletion.LocalMap

/-!
# Finite maps on maximal-ideal completions

For a local map with finite closed fiber, the maximal-ideal filtration on the
target is cofinal with the filtration induced from the source.  This leaf owns
the resulting comparison equivalence and the finite-module conclusion.

The algebra structure between the two completions remains a named value.  It
is deliberately not a global instance because the scalar map is determined by
the chosen local ring homomorphism.

@stack 0394
-/

@[expose] public section

noncomputable section

open IsLocalRing Ideal

universe u v

namespace AdicCompletion.LocalMap

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

local notation "mR" => maximalIdeal R
local notation "mS" => maximalIdeal S
local notation "mRS" => Ideal.map (algebraMap R S) mR
local notation "RCompletion" => AdicCompletion mR R
local notation "SCompletion" => AdicCompletion mS S
local notation "SmCompletion" => AdicCompletion mRS S

/-- The explicit algebra structure on maximal-ideal completions induced by the
chosen local algebra map. -/
noncomputable abbrev algebra : Algebra RCompletion SCompletion :=
  AdicCompletion.mapLocalAlgebra (algebraMap R S)

/-- Finite closed fiber implies that a positive power of the target maximal
ideal lies in the extended source maximal ideal. -/
theorem exists_pow_le_map
    (hmR : (maximalIdeal R).FG)
    (hfinite : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    ∃ n : ℕ, 0 < n ∧ mS ^ n ≤ mRS := sorry

/-- A chosen positive exponent comparing the target and source-induced
maximal-ideal filtrations. -/
noncomputable def exponent
    (hmR : (maximalIdeal R).FG)
    (hfinite : Module.Finite (R ⧸ mR) (S ⧸ mRS)) : ℕ :=
  Classical.choose (exists_pow_le_map hmR hfinite)

/-- The chosen filtration-comparison exponent is positive. -/
theorem exponent_pos
    (hmR : (maximalIdeal R).FG)
    (hfinite : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    0 < exponent hmR hfinite := sorry

/-- The chosen exponent has the required power containment. -/
theorem exponent_pow_le
    (hmR : (maximalIdeal R).FG)
    (hfinite : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    mS ^ exponent hmR hfinite ≤ mRS := sorry

/-- The extended source maximal ideal lies in the target maximal ideal. -/
theorem map_pow_one_le : mRS ^ 1 ≤ mS := sorry

/-- The canonical linear equivalence between the target maximal-ideal
completion and its completion along the extended source maximal ideal. -/
noncomputable def comparisonLinearEquiv
    (hmR : (maximalIdeal R).FG)
    (hfinite : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    SCompletion ≃ₗ[S] SmCompletion :=
  AdicCompletion.linearEquivOfPowLe mS mRS S
    (exponent hmR hfinite) 1
    (exponent_pos hmR hfinite) Nat.one_pos
    (exponent_pow_le hmR hfinite) map_pow_one_le

/-- The maximal-ideal completion comparison sends one to one. -/
theorem comparisonLinearEquiv_map_one
    (hmR : (maximalIdeal R).FG)
    (hfinite : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    comparisonLinearEquiv hmR hfinite 1 = 1 := sorry

/-- The maximal-ideal completion comparison preserves multiplication. -/
theorem comparisonLinearEquiv_map_mul
    (hmR : (maximalIdeal R).FG)
    (hfinite : Module.Finite (R ⧸ mR) (S ⧸ mRS))
    (x y : SCompletion) :
    comparisonLinearEquiv hmR hfinite (x * y) =
      comparisonLinearEquiv hmR hfinite x *
        comparisonLinearEquiv hmR hfinite y := sorry

/-- The algebra equivalence between the two cofinal completions of `S`. -/
@[stacks 0394 "cofinal completion comparison"]
noncomputable def comparisonEquiv
    (hmR : (maximalIdeal R).FG)
    (hfinite : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    SCompletion ≃ₐ[S] SmCompletion :=
  AlgEquiv.ofLinearEquiv
    (comparisonLinearEquiv hmR hfinite)
    (comparisonLinearEquiv_map_one hmR hfinite)
    (comparisonLinearEquiv_map_mul hmR hfinite)

/-- The completion comparison preserves the canonical image of `S`. -/
@[simp]
theorem comparisonEquiv_of
    (hmR : (maximalIdeal R).FG)
    (hfinite : Module.Finite (R ⧸ mR) (S ⧸ mRS)) (x : S) :
    comparisonEquiv hmR hfinite (AdicCompletion.of mS S x) =
      AdicCompletion.of mRS S x := sorry

/-- At every finite stage, the completion comparison intertwines `mapLocal`
with the quotient map induced by `R → S`. -/
theorem comparisonEquiv_eval
    (hmR : (maximalIdeal R).FG)
    (hfinite : Module.Finite (R ⧸ mR) (S ⧸ mRS))
    (n : ℕ) (c : RCompletion) :
    AdicCompletion.evalₐ mRS n
        (comparisonEquiv hmR hfinite
          (AdicCompletion.mapLocal (algebraMap R S) c)) =
      (Ideal.quotientMapₐ (mRS ^ n) (Algebra.ofId R S)
        ((Ideal.pow_right_mono
          (Ideal.le_comap_map : mR ≤ Ideal.comap (algebraMap R S) mRS) n).trans
          (Ideal.le_comap_pow (algebraMap R S) n)))
        (AdicCompletion.evalₐ mR n c) := sorry

/-- A local extension with finite closed fiber induces a finite map on
maximal-ideal completions.  The module structure is explicitly the one from
`AdicCompletion.mapLocal`. -/
@[stacks 0394 "finiteness of the completed extension"]
theorem finite
    (hmR : (maximalIdeal R).FG)
    (hfinite : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    @Module.Finite RCompletion SCompletion inferInstance inferInstance
      (algebra (R := R) (S := S)).toModule := sorry

end AdicCompletion.LocalMap
