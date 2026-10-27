/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Connection
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Epi
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.DividedPower.DeRham
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.FormComparison

/-!
# Exterior calculus for divided-power relative differentials

Ordinary relative exterior differentials descend through the divided-power relation
quotients. The normalized degree-one differential is the canonical divided-power
differential into the second exterior-power sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace DividedPowerScheme.RelativeDifferentials

variable (T : DividedPowerScheme.{u}) (S : Scheme.{u}) (f : T.scheme ⟶ S)

/-- Divided-power exterior forms, with the usual degree-zero and degree-one normalization. -/
abbrev formSheaf (n : ℕ) :=
  SheafOfModules.RingedSite.form T.scheme.sheaf (canonical T S f).module n

/-- The quotient from ordinary relative forms to divided-power exterior forms. -/
def quotientForm : (n : ℕ) →
    RingedSpace.DeRham.form f.toShHom n ⟶ formSheaf T S f n
  | 0 => (Scheme.RelativeDifferentials.formExteriorIso f 0).hom ≫
      (ExteriorPower.degreeZeroIso T.scheme.sheaf Ω[f.toShHom]).hom
  | 1 => (Scheme.RelativeDifferentials.formExteriorIso f 1).hom ≫
      (ExteriorPower.degreeOneIso T.scheme.sheaf Ω[f.toShHom]).inv ≫
        canonicalQuotient T S f
  | n + 2 => (Scheme.RelativeDifferentials.formExteriorIso f (n + 2)).hom ≫
      ExteriorPower.map T.scheme.sheaf (canonicalQuotient T S f) (n + 2)

set_option backward.privateInPublic true in
private theorem quotientForm_epi (n : ℕ) : Epi (quotientForm T S f n) := by
  have hq : Epi (canonicalQuotient T S f) := by
    change Epi (cokernel.π (relationInclusion T S f))
    infer_instance
  cases n with
  | zero => dsimp [quotientForm]; infer_instance
  | succ n =>
    cases n with
    | zero =>
      exact CategoryTheory.epi_comp' inferInstance
        (CategoryTheory.epi_comp' inferInstance hq)
    | succ n =>
      exact CategoryTheory.epi_comp' inferInstance
        (@ExteriorPower.map_epi _ _ _ _ _ _ T.scheme.sheaf _ _ (canonicalQuotient T S f) (n + 2) hq)

/-- The quotient from ordinary forms, regarded as a morphism over the base coefficient sheaf. -/
def restrictedQuotientForm (n : ℕ) :=
  (coefficientRestriction T S f).map (quotientForm T S f n)

set_option backward.privateInPublic true in
private theorem restrictedQuotientForm_epi (n : ℕ) :
    Epi (restrictedQuotientForm T S f n) :=
  @Functor.map_epi _ _ _ _ (coefficientRestriction T S f) inferInstance _ _
    (quotientForm T S f n) (quotientForm_epi T S f n)

/-- The ordinary exterior differential annihilates the divided-power relation kernel after
projection of its values to divided-power forms. -/
theorem quotientFormDifferential_relations (n : ℕ) :
    kernel.ι (restrictedQuotientForm T S f n) ≫
      RingedSpace.DeRham.d f.toShHom n ≫ restrictedQuotientForm T S f (n + 1) = 0 := sorry

set_option backward.privateInPublic true in
private def descendedDifferential (n : ℕ) :
    (coefficientRestriction T S f).obj (formSheaf T S f n) ⟶
      (coefficientRestriction T S f).obj (formSheaf T S f (n + 1)) :=
  @Abelian.epiDesc _ _ _ _ _ (restrictedQuotientForm T S f n)
    (restrictedQuotientForm_epi T S f n) _
    (RingedSpace.DeRham.d f.toShHom n ≫ restrictedQuotientForm T S f (n + 1))
    (quotientFormDifferential_relations T S f n)

set_option backward.privateInPublic true in
/-- The divided-power exterior differential, using the canonical degree-one differential
and quotient descent in all other degrees. -/
def quotientFormDifferential : (n : ℕ) →
    (coefficientRestriction T S f).obj (formSheaf T S f n) ⟶
      (coefficientRestriction T S f).obj (formSheaf T S f (n + 1))
  | 0 => descendedDifferential T S f 0
  | 1 => d T S f
  | n + 2 => descendedDifferential T S f (n + 2)

/-- The descended exterior differential extends the universal divided-power derivation and
commutes with the ordinary-to-divided-power quotient maps. -/
theorem quotientFormDifferential_laws :
    (∀ (U : (Opens T.scheme)ᵒᵖ) (a : T.scheme.presheaf.obj U),
      (quotientFormDifferential T S f 0).val.app U a =
        (canonicalDerivation T S f).toDerivation.d a) ∧
    (∀ n, restrictedQuotientForm T S f n ≫ quotientFormDifferential T S f n =
      RingedSpace.DeRham.d f.toShHom n ≫ restrictedQuotientForm T S f (n + 1)) := sorry

/-- The divided-power exterior differential satisfies the coefficient Leibniz rule. -/
theorem exteriorCalculus_d_smul (n : ℕ) (U : (Opens T.scheme)ᵒᵖ)
    (a : T.scheme.presheaf.obj U) (ω : (formSheaf T S f n).val.obj U) :
    (quotientFormDifferential T S f n).val.app U (a • ω) =
      ((formSheaf T S f (n + 1)).val.obj U).isModule.smul a
        ((quotientFormDifferential T S f n).val.app U ω) +
      (eqToHom (congrArg (formSheaf T S f) (Nat.add_comm 1 n))).val.app U
        (formWedgeApp (canonical T S f).module 1 n U
          ((canonicalDerivation T S f).toDerivation.d a) ω) := sorry

/-- The divided-power exterior differential is a graded derivation for wedge multiplication. -/
theorem exteriorCalculus_d_wedge (i j : ℕ) (U : (Opens T.scheme)ᵒᵖ)
    (α : (formSheaf T S f i).val.obj U) (β : (formSheaf T S f j).val.obj U) :
    (quotientFormDifferential T S f (i + j)).val.app U
        (formWedgeApp (canonical T S f).module i j U α β) =
      (eqToHom (congrArg (formSheaf T S f)
        (by omega : i + 1 + j = i + j + 1))).val.app U
        (formWedgeApp (canonical T S f).module (i + 1) j U
          ((quotientFormDifferential T S f i).val.app U α) β) +
      (-1 : ℤ) ^ i •
        (eqToHom (congrArg (formSheaf T S f)
          (by omega : i + (j + 1) = i + j + 1))).val.app U
          (formWedgeApp (canonical T S f).module i (j + 1) U α
            ((quotientFormDifferential T S f j).val.app U β)) := sorry

/-- Consecutive divided-power exterior differentials compose to zero. -/
theorem exteriorCalculus_d_sq (n : ℕ) :
    quotientFormDifferential T S f n ≫ quotientFormDifferential T S f (n + 1) = 0 := sorry

/-- The canonical exterior calculus on divided-power relative differential sheaves. -/
def exteriorCalculus :
    SheafOfModules.RingedSite.ExteriorCalculus.{u, u}
      (RingedSpace.DeRham.structureMap f.toShHom) (canonical T S f).module
      (canonicalDerivation T S f).toDerivation where
  d := quotientFormDifferential T S f
  d_zero := (quotientFormDifferential_laws T S f).1
  d_smul := exteriorCalculus_d_smul T S f
  d_wedge := exteriorCalculus_d_wedge T S f
  d_sq := exteriorCalculus_d_sq T S f

/-- On compatible affine opens, the sheaf differential agrees with the canonical
ring-level divided-power exterior calculus under every derivation-compatible comparison. -/
theorem exteriorCalculus_affine (W : T.scheme.affineOpens) (V : S.affineOpens)
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
            (affineComparison_isIso T S f W)) ((quotientFormDifferential T S f 1).val.app (op W.1) ω)) =
          DPPolynomial.DeRham.canonicalFamily Γ(S, V.1) Γ(T.scheme, W.1)
            (T.dividedPowers W) 1 (eΩ ω) := sorry

end DividedPowerScheme.RelativeDifferentials
