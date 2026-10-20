/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Finsupp
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.QuotientByIdeal

/-!
# Finitely supported free modules over quotient rings

This leaf packages coefficientwise reduction of a free `Finsupp` module
along a quotient map.  It deliberately works for a two-sided ideal in an
arbitrary ring, since the free-module presentation is also used before
commutativity hypotheses are available.
-/

@[expose] public section

universe u v

namespace Ideal.Quotient.Finsupp

variable {R : Type u} [Ring R]
variable (I : Ideal R) [I.IsTwoSided]
variable (ι : Type v)

/-- Coefficientwise reduction from the free `R`-module on `ι` to the free
`R ⧸ I`-module, viewed by restriction of scalars as an `R`-linear map. -/
@[stacks 07LV "finsupp coefficient quotient"]
noncomputable abbrev coeffMap : (ι →₀ R) →ₗ[R] ι →₀ (R ⧸ I) :=
  Finsupp.mapRange.linearMap (I.mkQ : R →ₗ[R] R ⧸ I)

/-- Coefficientwise reduction sends the `i`-th coefficient to its quotient
class modulo `I`. -/
@[simp, stacks 07LV "finsupp coefficient quotient on coefficients"]
theorem coeffMap_apply (x : ι →₀ R) (i : ι) :
    coeffMap I ι x i = Ideal.Quotient.mk I (x i) := sorry

/-- Coefficientwise reduction on a free `Finsupp` module is surjective. -/
@[stacks 07LV "finsupp coefficient quotient surjective"]
theorem coeffMap_surjective :
    Function.Surjective (coeffMap I ι) := sorry

/-- The kernel of coefficientwise reduction is the ideal multiple of the
free source module. -/
@[stacks 07LV "finsupp coefficient quotient kernel"]
theorem ker_coeffMap :
    LinearMap.ker (coeffMap I ι) = I • (⊤ : Submodule R (ι →₀ R)) := sorry

/-- Quotienting a free `Finsupp` module by `I • ⊤` is canonically the free
module over `R ⧸ I`.  The equivalence is constructed directly from
coefficientwise reduction; its non-Prop data does not depend on deferred
proof declarations in this file. -/
@[stacks 07LV "finsupp free quotient equivalence"]
noncomputable def quotientLinearEquiv :
    ((ι →₀ R) ⧸ (I • (⊤ : Submodule R (ι →₀ R)))) ≃ₗ[R]
      ι →₀ (R ⧸ I) :=
  let hsub :
      Finsupp.submodule (fun _ : ι => I) =
        I • (⊤ : Submodule R (ι →₀ R)) := by
    ext x
    constructor
    · intro hx
      have hsum : x = x.sum fun i a => a • Finsupp.single i (1 : R) := by
        ext i
        simp
      rw [hsum]
      refine Submodule.sum_mem _ fun i _ => ?_
      exact Submodule.smul_mem_smul (hx i)
        (by simp : Finsupp.single i (1 : R) ∈ (⊤ : Submodule R (ι →₀ R)))
    · intro hx i
      have h_eval :
          (Finsupp.lapply (R := R) (M := R) i) x ∈
            I • (⊤ : Submodule R R) :=
        (Submodule.smul_top_le_comap_smul_top I
          (Finsupp.lapply (R := R) (M := R) i)) hx
      simpa using h_eval
  let hker :
      LinearMap.ker (coeffMap I ι) = I • (⊤ : Submodule R (ι →₀ R)) := by
    change LinearMap.ker
        (Finsupp.mapRange.linearMap (I.mkQ : R →ₗ[R] R ⧸ I)) = _
    rw [Finsupp.ker_mapRange]
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hsub
  let hsurj : Function.Surjective (coeffMap I ι) := by
    change Function.Surjective (Finsupp.mapRange I.mkQ I.mkQ.map_zero)
    exact Finsupp.mapRange_surjective I.mkQ I.mkQ.map_zero I.mkQ_surjective
  (Submodule.quotEquivOfEq _ _ hker.symm).trans <|
    LinearMap.quotKerEquivOfSurjective (coeffMap I ι) hsurj

/-- `quotientLinearEquiv` sends a quotient representative to the
coefficientwise reduced finitely supported vector. -/
@[simp, stacks 07LV "finsupp free quotient equivalence on representatives"]
theorem quotientLinearEquiv_apply_mk (x : ι →₀ R) :
    quotientLinearEquiv I ι (Submodule.Quotient.mk x) = coeffMap I ι x := sorry

/-- The inverse of `quotientLinearEquiv` sends a coefficientwise quotient
of a finitely supported vector back to its quotient class. -/
@[simp, stacks 07LV "finsupp free quotient inverse on representatives"]
theorem quotientLinearEquiv_symm_apply_coeffMap (x : ι →₀ R) :
    (quotientLinearEquiv I ι).symm (coeffMap I ι x) =
      Submodule.Quotient.mk x := sorry

end Ideal.Quotient.Finsupp
