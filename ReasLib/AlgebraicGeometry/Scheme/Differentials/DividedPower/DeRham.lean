/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.DividedPower.Canonical
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.DegreeOne
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Exact
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.Calculus
public import ReasLib.LinearAlgebra.ExteriorPower.LeftTensor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# The degree-one divided-power de Rham differential

The ordinary relative differential descends through the divided-power relation quotient
with values in its second exterior-power sheaf. The resulting differential is linear over
the inverse-image base structure sheaf and satisfies the relative Leibniz rule.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

universe u

noncomputable section

namespace DividedPowerScheme.RelativeDifferentials

variable (T : DividedPowerScheme.{u}) (S : Scheme.{u}) (f : T.scheme ⟶ S)

/-- The second exterior-power sheaf of canonical divided-power relative differentials. -/
abbrev twoForms : T.scheme.Modules :=
  ExteriorPower.sheaf T.scheme.sheaf (canonical T S f).module 2

/-- The canonical comparison from exterior powers of sections to sections of exterior powers. -/
def exteriorComparison (U : (Opens T.scheme)ᵒᵖ) :
    (PresheafOfModules.ExteriorPower.sectionObj T.scheme.sheaf.obj
      (canonical T S f).module.val U).exteriorPower 2 ⟶
      (twoForms T S f).val.obj U :=
  (moduleSheafificationUnitToVal T.scheme.sheaf
    (ExteriorPower.presheaf T.scheme.sheaf (canonical T S f).module 2)).app U

/-- The wedge of two differential sections, valued in the exterior-power sheaf. -/
def wedgeApp (U : (Opens T.scheme)ᵒᵖ) :
    (canonical T S f).module.val.obj U →ₗ[T.scheme.presheaf.obj U]
      (canonical T S f).module.val.obj U →ₗ[T.scheme.presheaf.obj U]
        (twoForms T S f).val.obj U := by
  refine {
    toFun ω := (exteriorComparison T S f U).hom.comp (exteriorPower.leftWedgeOne ω)
    map_add' := ?_
    map_smul' := ?_ }
  all_goals sorry

/-- The wedge of a differential section with itself vanishes. -/
theorem wedgeApp_alternating (U : (Opens T.scheme)ᵒᵖ)
    (ω : (canonical T S f).module.val.obj U) : wedgeApp T S f U ω ω = 0 := sorry

/-- Restriction to the inverse-image base structure sheaf. -/
abbrev coefficientRestriction :=
  restrictionAlong.{u, u, u, u} (RingedSpace.DeRham.structureMap f.toShHom)

/-- The ordinary differential followed by projection of its two-form values to
divided-power two-forms, with scalars restricted to the base. -/
def ordinaryD :
    (coefficientRestriction T S f).obj Ω[f.toShHom] ⟶
      (coefficientRestriction T S f).obj (twoForms T S f) := by
  let φ := RingedSpace.DeRham.structureMap f.toShHom
  let P := PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom
  let toOne : P ⟶ PresheafOfModules.DeRham.form φ.hom 1 :=
    { app := fun U ↦ ModuleCat.ofHom
        (LinearEquiv.ofBijective
          (@KaehlerDifferential.DeRham.toExterior ((RingedSpace.DeRham.coefficients f.toShHom).obj.obj U)
            (T.scheme.presheaf.obj U) inferInstance inferInstance
            (φ.hom.app U).hom.toAlgebra 1).hom
          (@KaehlerDifferential.DeRham.toExterior_bijective ((RingedSpace.DeRham.coefficients f.toShHom).obj.obj U)
            (T.scheme.presheaf.obj U) inferInstance inferInstance
            (φ.hom.app U).hom.toAlgebra 1)).symm.toLinearMap
      naturality := ?_ }
  let quotientSections : P ⟶ (canonical T S f).module.val :=
    moduleSheafificationUnitToVal T.scheme.sheaf P ≫ (canonical T S f).quotient.val
  let toTwo : PresheafOfModules.DeRham.form φ.hom 2 ⟶
      (twoForms T S f).val :=
    { app := fun U ↦
        (@KaehlerDifferential.DeRham.toExterior ((RingedSpace.DeRham.coefficients f.toShHom).obj.obj U)
          (T.scheme.presheaf.obj U) inferInstance inferInstance
          (φ.hom.app U).hom.toAlgebra 2) ≫
        ModuleCat.exteriorPower.map (quotientSections.app U) 2 ≫
        exteriorComparison T S f U
      naturality := ?_ }
  exact (coefficientRestriction T S f).map ((moduleSheafification T.scheme.sheaf).map toOne) ≫
    RingedSpace.DeRham.d f.toShHom 1 ≫
    (coefficientRestriction T S f).map
      ((moduleSheafificationHomEquiv T.scheme.sheaf _ _).symm toTwo)
  all_goals sorry

/-- Differentiating a divided-power relation gives zero in divided-power two-forms. -/
theorem relation_d_zero :
    (coefficientRestriction T S f).map (relationInclusion T S f) ≫
      ordinaryD T S f = 0 := sorry

/-- The degree-one divided-power de Rham differential, descended through the relation quotient. -/
def d :
    (coefficientRestriction T S f).obj (canonical T S f).module ⟶
      (coefficientRestriction T S f).obj (twoForms T S f) :=
  (PreservesCokernel.iso (coefficientRestriction T S f) (relationInclusion T S f)).hom ≫
    cokernel.desc _ (ordinaryD T S f) (relation_d_zero T S f)

/-- The additive section map underlying the divided-power de Rham differential. -/
def dApp (U : (Opens T.scheme)ᵒᵖ) :
    (canonical T S f).module.val.obj U →+ (twoForms T S f).val.obj U :=
  ((d T S f).val.app U).hom.toAddMonoidHom

/-- The sectionwise universal divided-power derivation. -/
def derivationApp (U : (Opens T.scheme)ᵒᵖ) :
    T.scheme.presheaf.obj U →+ (canonical T S f).module.val.obj U :=
  (canonicalDerivation T S f).toDerivation.d (X := U)

/-- The divided-power differential satisfies the coefficient Leibniz rule. -/
theorem d_smul (U : (Opens T.scheme)ᵒᵖ) (a : T.scheme.presheaf.obj U)
    (ω : (canonical T S f).module.val.obj U) :
    dApp T S f U (a • ω) =
      a • dApp T S f U ω + wedgeApp T S f U (derivationApp T S f U a) ω := sorry

/-- Exact divided-power one-forms have zero differential. -/
theorem d_d (U : (Opens T.scheme)ᵒᵖ) (a : T.scheme.presheaf.obj U) :
    dApp T S f U (derivationApp T S f U a) = 0 := sorry

/-- Differentiation of a finite sum of basic one-forms differentiates their coefficients. -/
theorem d_sum (U : (Opens T.scheme)ᵒᵖ) {ι : Type*} (s : Finset ι)
    (a b : ι → T.scheme.presheaf.obj U) :
    dApp T S f U (∑ i ∈ s, a i • derivationApp T S f U (b i)) =
      ∑ i ∈ s, wedgeApp T S f U (derivationApp T S f U (a i))
        (derivationApp T S f U (b i)) := sorry

/-- On affine opens, exterior powers of canonical differential sections compute the
sections of the exterior-power sheaf. -/
theorem affineComparison_isIso (W : T.scheme.affineOpens) :
    IsIso (exteriorComparison T S f (op W.1)) := sorry

/-- On compatible affine opens, the sheaf differential agrees with the canonical
ring-level divided-power exterior calculus under every derivation-compatible comparison. -/
theorem d_affine (W : T.scheme.affineOpens) (V : S.affineOpens)
    (hWV : W.1 ≤ f ⁻¹ᵁ V.1) :
    -- Local instance justification (defeq pin): the explicit affine section morphism determines the algebra used by the divided-power differential comparison.
    letI := (f.appLE V.1 W.1 hWV).hom.toAlgebra
    ∀ (eΩ : Γ((canonical T S f).module, W.1) ≃ₗ[Γ(T.scheme, W.1)]
        KaehlerDifferential.DeRham.dividedPowerDifferential
          (f.appLE V.1 W.1 hWV).hom (T.dividedPowers W)),
      (∀ a : Γ(T.scheme, W.1),
        eΩ (derivationApp T S f (op W.1) a) =
          KaehlerDifferential.DeRham.dividedPowerDifferentialDerivation
            (f.appLE V.1 W.1 hWV).hom (T.dividedPowers W) a) →
      ∀ ω : Γ((canonical T S f).module, W.1),
        ModuleCat.exteriorPower.map (ModuleCat.ofHom eΩ.toLinearMap) 2
          ((@inv _ _ _ _ (exteriorComparison T S f (op W.1))
            (affineComparison_isIso T S f W)) (dApp T S f (op W.1) ω)) =
          DPPolynomial.DeRham.canonicalFamily Γ(S, V.1) Γ(T.scheme, W.1)
            (T.dividedPowers W) 1 (eΩ ω) := sorry

end DividedPowerScheme.RelativeDifferentials
