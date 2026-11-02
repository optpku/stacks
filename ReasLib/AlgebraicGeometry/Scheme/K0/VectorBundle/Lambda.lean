/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.DegreeZero
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Properties
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Lambda operations on vector-bundle K-theory

The total exterior-power series is descended through the short-exact relations defining
vector-bundle `K₀`. Its coefficients give the individual lambda operations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.VectorBundleK0

variable {X Y : Scheme.{u}}

/-- The `r`-th exterior power of a finite locally free module, as a vector bundle. -/
noncomputable def exteriorPowerObj (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) (r : ℕ) :
    ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) :=
  ⟨RingedSpace.ExteriorPower.sheaf E.obj r,
    @SheafOfModules.RingedSite.ExteriorPower.isFiniteLocallyFree
      _ _ _ _ _ _ _ E.obj r _ _ E.property⟩

/-- The underlying module of `exteriorPowerObj X E r` is `Λ[r] E.obj`. -/
theorem exteriorPowerObj_obj (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) (r : ℕ) :
    (exteriorPowerObj X E r).obj = RingedSpace.ExteriorPower.sheaf E.obj r := rfl

/-- The total exterior-power series of a finite locally free module. -/
noncomputable def totalExteriorPowerSeries (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    PowerSeries (VectorBundleK0 X) :=
  PowerSeries.mk fun r ↦ ObjectProperty.GrothendieckGroup.of
    (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
    (exteriorPowerObj X E r)

/-- The `r`-th coefficient of the total exterior-power series is the class of
`exteriorPowerObj X E r`. -/
theorem totalExteriorPowerSeries_coeff (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) (r : ℕ) :
    PowerSeries.coeff r (totalExteriorPowerSeries X E) =
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
        (exteriorPowerObj X E r) := by
  exact PowerSeries.coeff_mk r _

/-- The constant coefficient of the total exterior-power series is one. -/
theorem totalExteriorPowerSeries_constantCoeff (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    PowerSeries.constantCoeff (totalExteriorPowerSeries X E) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, totalExteriorPowerSeries_coeff]
  change ObjectProperty.GrothendieckGroup.of
    (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
      (exteriorPowerObj X E 0) =
    ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) (unitObject X)
  let M : X.Modules := Limits.terminal X.Modules
  have hM : Limits.IsZero M := by
    apply (Limits.IsZero.iff_id_eq_zero _).2
    exact (Limits.terminalIsTerminal (C := X.Modules)).hom_ext _ _
  letI : SheafOfModules.IsFiniteLocallyFree
      (SheafOfModules.unit X.ringCatSheaf) := (unitObject X).property
  let r : Retract M (SheafOfModules.unit X.ringCatSheaf) :=
    { i := 0, r := 0, retract := hM.eq_of_src _ _ }
  let Z : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) :=
    ⟨M, SheafOfModules.IsFiniteLocallyFree.ofRetract
      (X := X.toLocallyRingedSpace) r⟩
  exact ObjectProperty.GrothendieckGroup.of_iso Z hM
    (ObjectProperty.isoMk _
      (SheafOfModules.RingedSite.ExteriorPower.degreeZeroIso X.sheaf E.obj))

/-- The total exterior-power series, bundled with its explicit formal inverse. -/
noncomputable def totalExteriorPowerUnit (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    (PowerSeries (VectorBundleK0 X))ˣ :=
  { val := totalExteriorPowerSeries X E
    inv := PowerSeries.invOfUnit (totalExteriorPowerSeries X E) 1
    val_inv := PowerSeries.mul_invOfUnit (totalExteriorPowerSeries X E) 1
      (totalExteriorPowerSeries_constantCoeff X E)
    inv_val := PowerSeries.invOfUnit_mul (totalExteriorPowerSeries X E) 1
      (totalExteriorPowerSeries_constantCoeff X E) }

/-- The value of `totalExteriorPowerUnit X E` is the total exterior-power series. -/
theorem totalExteriorPowerUnit_val (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    (totalExteriorPowerUnit X E).val = totalExteriorPowerSeries X E := rfl

/-- Total exterior-power units are multiplicative on ambient short exact sequences. -/
theorem totalExteriorPowerUnit_shortExact (X : Scheme.{u})
    (S : ShortComplex (ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)))
    (hS : (S.map
      (ObjectProperty.ι
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules))).ShortExact) :
    totalExteriorPowerUnit X S.X₂ =
      totalExteriorPowerUnit X S.X₁ * totalExteriorPowerUnit X S.X₃ := sorry

/-- The short-exact relations defining vector-bundle `K₀` lie in the kernel of the
total exterior-power invariant. -/
theorem relations_le_ker_totalExteriorPower (X : Scheme.{u}) :
    ObjectProperty.GrothendieckGroup.relations
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) ≤
      (FreeAbelianGroup.lift fun E : ObjectProperty.FullSubcategory
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) ↦
        Additive.ofMul (totalExteriorPowerUnit X E)).ker := by
  apply (AddSubgroup.closure_le _).2
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change (FreeAbelianGroup.lift fun E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) ↦
    Additive.ofMul (totalExteriorPowerUnit X E))
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ -
        FreeAbelianGroup.of S.X₃) = 0
  simp only [map_sub, FreeAbelianGroup.lift_apply_of]
  rw [totalExteriorPowerUnit_shortExact X S hS, ofMul_mul]
  simp

/-- The total exterior-power operation on vector-bundle `K₀`, valued in additive
power-series units. -/
noncomputable def totalExteriorPower (X : Scheme.{u}) :
    VectorBundleK0 X →+ Additive ((PowerSeries (VectorBundleK0 X))ˣ) :=
  ObjectProperty.GrothendieckGroup.lift
    (fun E ↦ Additive.ofMul (totalExteriorPowerUnit X E))
    (relations_le_ker_totalExteriorPower X)

/-- The total exterior-power operation evaluates on a vector-bundle generator as its
total exterior-power unit. -/
theorem totalExteriorPower_of (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    totalExteriorPower X (ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
      Additive.ofMul (totalExteriorPowerUnit X E) := by
  exact FreeAbelianGroup.lift_apply_of _ E

/-- The `r`-th lambda operation on vector-bundle `K₀`. -/
noncomputable def lambda (X : Scheme.{u}) (r : ℕ) : VectorBundleK0 X → VectorBundleK0 X :=
  fun a ↦ PowerSeries.coeff r (totalExteriorPower X a).toMul.val

/-- The `r`-th lambda operation sends a vector-bundle generator to the class of its
`r`-th exterior power. -/
theorem lambda_of (X : Scheme.{u}) (r : ℕ)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    lambda X r (ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
        (exteriorPowerObj X E r) := by
  unfold lambda
  rw [totalExteriorPower_of]
  exact totalExteriorPowerSeries_coeff X E r

/-- Lambda operations turn addition into the Cauchy convolution of coefficients. -/
theorem lambda_add (X : Scheme.{u}) (r : ℕ) (a b : VectorBundleK0 X) :
    lambda X r (a + b) =
      ∑ ij : Finset.antidiagonal r, lambda X ij.1.1 a * lambda X ij.1.2 b := by
  unfold lambda
  rw [map_add, toMul_add, Units.val_mul, PowerSeries.coeff_mul]
  exact (Finset.sum_attach _ _).symm

/-- Lambda operations on vector-bundle `K₀` commute with pullback of schemes. -/
theorem lambda_pullback (f : X ⟶ Y) (r : ℕ) (a : VectorBundleK0 Y) :
    pullback f (lambda Y r a) = lambda X r (pullback f a) := sorry

end AlgebraicGeometry.Scheme.VectorBundleK0
