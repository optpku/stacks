/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers
public import ReasLib.RingTheory.DividedPowers.TrivSqZeroExt
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section
open KaehlerDifferential.DeRham
universe u
namespace CrystallinePDDeRham
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J)

/-- Right scalar multiplication on PD forms is the same actual scalar
action as the left action, since the coefficient ring is commutative. -/
noncomputable instance oneFormsOppositeModule : Module Bᵐᵒᵖ (ambientDividedPowerDifferential (A := A) δ) :=
  Module.compHom (ambientDividedPowerDifferential (A := A) δ)
    ((RingHom.id B).fromOpposite (fun x y ↦ Commute.all x y))

/-- The opposite action used by the PD square-zero extension is central. -/
instance oneFormsCentralScalar : IsCentralScalar B (ambientDividedPowerDifferential (A := A) δ) where
  op_smul_eq_smul _ _ := rfl

/-- The quotient enforces precisely the divided-power differential formula. -/
theorem derivation_dpow (n : ℕ) (x : B) (hx : x ∈ J) (hn : 1 ≤ n) :
    (ambientDividedPowerDifferentialDerivation (A := A) δ)
      (δ.dpow n x) = δ.dpow (n - 1) x • (ambientDividedPowerDifferentialDerivation (A := A) δ) x := sorry

section SquareZero
variable [Module Bᵐᵒᵖ (ambientDividedPowerDifferential (A := A) δ)]
variable [IsCentralScalar B (ambientDividedPowerDifferential (A := A) δ)]

/-- Projection of the PD square-zero extension onto the original closed fibre. -/
noncomputable def closedFibreMap : TrivSqZeroExt B (ambientDividedPowerDifferential (A := A) δ) →+* B ⧸ J :=
  (Ideal.Quotient.mk J).comp (TrivSqZeroExt.fstHom B B (ambientDividedPowerDifferential (A := A) δ)).toRingHom

/-- Every closed-fibre element lifts through the first-coordinate inclusion. -/
theorem closedFibreMap_surjective : Function.Surjective (closedFibreMap A B δ) := by
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨TrivSqZeroExt.inl b, rfl⟩

/-- The kernel of projection to the closed fibre is exactly the DP ideal,
including the whole square-zero differential factor. -/
theorem closedFibreMap_kernel :
    RingHom.ker (closedFibreMap A B δ) = DividedPowers.TrivSqZeroExt.ideal (ambientDividedPowerDifferential (A := A) δ) J := by
  ext x
  change Ideal.Quotient.mk J x.fst = 0 ↔ x.fst ∈ J
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The square-zero PD thickening has the same closed fibre, through its
actual quotient map. No arbitrary scheme or ring identification is chosen. -/
noncomputable def closedFibreEquiv :
    TrivSqZeroExt B (ambientDividedPowerDifferential (A := A) δ) ⧸
        DividedPowers.TrivSqZeroExt.ideal (ambientDividedPowerDifferential (A := A) δ) J ≃+* B ⧸ J :=
  (Ideal.quotEquivOfEq (closedFibreMap_kernel A B δ).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := closedFibreMap A B δ)
      (closedFibreMap_surjective A B δ))

/-- The second PD infinitesimal lift, built with PD rather than ordinary
Kähler differentials. Its two coordinates are exactly b and db. -/
noncomputable def differentialLift : B →+* TrivSqZeroExt B (ambientDividedPowerDifferential (A := A) δ) where
  toFun b := TrivSqZeroExt.inl b + TrivSqZeroExt.inr ((ambientDividedPowerDifferentialDerivation (A := A) δ) b)
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

/-- The PD derivation law makes the infinitesimal lift a PD morphism. -/
theorem differentialLift_preservesDP :
    DividedPowers.IsDPMorphism δ (DividedPowers.TrivSqZeroExt.dividedPowers (ambientDividedPowerDifferential (A := A) δ) δ)
      (differentialLift A B δ) := sorry

/-- The actual bundled PD lift used to construct finite-stage stratification. -/
noncomputable def differentialDPLift :
    DividedPowers.DPMorphism δ (DividedPowers.TrivSqZeroExt.dividedPowers (ambientDividedPowerDifferential (A := A) δ) δ) :=
  DividedPowers.DPMorphism.mk' (differentialLift_preservesDP A B δ)

end SquareZero

end CrystallinePDDeRham
