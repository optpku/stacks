/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.BaseChange
public import ReasLib.Algebra.Module.RelativeDualizing.Comparison

@[expose] public section

open AlgebraicGeometry

universe u v

namespace Algebra.RelativeDualizingModule

/-- Base change is natural with respect to compatible refinements of finite open models. -/
theorem baseChangeOf_comparison
    (A A₁ : Type u) (P₀ P₁ Q₀ Q₁ B B₁ : Type v)
    [CommRing A] [CommRing A₁] [CommRing P₀] [CommRing P₁]
    [CommRing Q₀] [CommRing Q₁] [CommRing B] [CommRing B₁]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsNoetherianRing A₁] [IsNoetherianRing B₁]
    [Algebra A P₀] [Algebra P₀ B] [Algebra A B] [IsScalarTower A P₀ B]
    [Algebra A P₁] [Algebra P₁ B] [IsScalarTower A P₁ B]
    [Algebra A₁ Q₀] [Algebra Q₀ B₁] [Algebra A₁ B₁] [IsScalarTower A₁ Q₀ B₁]
    [Algebra A₁ Q₁] [Algebra Q₁ B₁] [IsScalarTower A₁ Q₁ B₁]
    [Algebra A A₁] [Algebra B B₁]
    [Algebra P₀ Q₀] [Algebra A Q₀] [IsScalarTower A P₀ Q₀]
    [IsScalarTower A A₁ Q₀]
    [Algebra P₁ Q₁] [Algebra A Q₁] [IsScalarTower A P₁ Q₁]
    [IsScalarTower A A₁ Q₁]
    [Algebra A B₁] [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁]
    [Algebra P₀ B₁] [IsScalarTower P₀ B B₁] [IsScalarTower P₀ Q₀ B₁]
    [Algebra P₁ B₁] [IsScalarTower P₁ B B₁] [IsScalarTower P₁ Q₁ B₁]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    (h_quasiFinite₁ : Algebra.FiniteType.QuasiFinite A₁ B₁)
    [Module.Finite A P₀] [Module.Finite A P₁]
    [Module.Finite A₁ Q₀] [Module.Finite A₁ Q₁]
    (h_openP₀ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap P₀ B))))
    (h_openP₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap P₁ B))))
    (h_openQ₀ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Q₀ B₁))))
    (h_openQ₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Q₁ B₁))))
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B B₁).toLinearMap)
    (h_finiteModel₀ : IsBaseChange A₁
      (IsScalarTower.toAlgHom A P₀ Q₀).toLinearMap)
    (h_finiteModel₁ : IsBaseChange A₁
      (IsScalarTower.toAlgHom A P₁ Q₁).toLinearMap)
    (i : P₀ →ₐ[A] P₁) (i₁ : Q₀ →ₐ[A₁] Q₁)
    (h_triangle : (algebraMap P₁ B).comp i.toRingHom = algebraMap P₀ B)
    (h_triangle₁ : (algebraMap Q₁ B₁).comp i₁.toRingHom = algebraMap Q₀ B₁)
    (x : RelativeDualizingModule.of A P₁ B h_quasiFinite h_openP₁) :
    baseChangeOf A A₁ P₀ B Q₀ B₁ h_quasiFinite h_quasiFinite₁
        h_openP₀ h_openQ₀ h_baseChange h_finiteModel₀
        (comparison A P₀ P₁ B h_quasiFinite h_openP₀ h_openP₁ i h_triangle x) =
      comparison A₁ Q₀ Q₁ B₁ h_quasiFinite₁ h_openQ₀ h_openQ₁ i₁ h_triangle₁
        (baseChangeOf A A₁ P₁ B Q₁ B₁ h_quasiFinite h_quasiFinite₁
          h_openP₁ h_openQ₁ h_baseChange h_finiteModel₁ x) := sorry

/-- Successive base changes agree with the direct base change under compatible
base-change hypotheses. -/
theorem baseChangeOf_trans
    (A A₁ A₂ : Type u) (P P₁ P₂ B B₁ B₂ : Type v)
    [CommRing A] [CommRing A₁] [CommRing A₂]
    [CommRing P] [CommRing P₁] [CommRing P₂]
    [CommRing B] [CommRing B₁] [CommRing B₂]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsNoetherianRing A₁] [IsNoetherianRing B₁]
    [IsNoetherianRing A₂] [IsNoetherianRing B₂]
    [Algebra A P] [Algebra P B] [Algebra A B] [IsScalarTower A P B]
    [Algebra A₁ P₁] [Algebra P₁ B₁] [Algebra A₁ B₁] [IsScalarTower A₁ P₁ B₁]
    [Algebra A₂ P₂] [Algebra P₂ B₂] [Algebra A₂ B₂] [IsScalarTower A₂ P₂ B₂]
    [Algebra A A₁] [Algebra A₁ A₂] [Algebra A A₂] [IsScalarTower A A₁ A₂]
    [Algebra P P₁] [Algebra P₁ P₂] [Algebra P P₂] [IsScalarTower P P₁ P₂]
    [Algebra B B₁] [Algebra B₁ B₂] [Algebra B B₂] [IsScalarTower B B₁ B₂]
    [Algebra A P₁] [IsScalarTower A P P₁] [IsScalarTower A A₁ P₁]
    [Algebra A B₁] [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁]
    [Algebra P B₁] [IsScalarTower P B B₁] [IsScalarTower P P₁ B₁]
    [Algebra A₁ P₂] [IsScalarTower A₁ P₁ P₂] [IsScalarTower A₁ A₂ P₂]
    [Algebra A₁ B₂] [IsScalarTower A₁ B₁ B₂] [IsScalarTower A₁ A₂ B₂]
    [Algebra P₁ B₂] [IsScalarTower P₁ B₁ B₂] [IsScalarTower P₁ P₂ B₂]
    [Algebra A P₂] [IsScalarTower A P P₂] [IsScalarTower A A₂ P₂]
    [Algebra A B₂] [IsScalarTower A B B₂] [IsScalarTower A A₂ B₂]
    [Algebra P B₂] [IsScalarTower P B B₂] [IsScalarTower P P₂ B₂]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    (h_quasiFinite₁ : Algebra.FiniteType.QuasiFinite A₁ B₁)
    (h_quasiFinite₂ : Algebra.FiniteType.QuasiFinite A₂ B₂)
    [Module.Finite A P] [Module.Finite A₁ P₁] [Module.Finite A₂ P₂]
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap P B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap P₁ B₁))))
    (h_open₂ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap P₂ B₂))))
    (h_baseChange₀₁ : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B B₁).toLinearMap)
    (h_baseChange₁₂ : IsBaseChange A₂
      (IsScalarTower.toAlgHom A₁ B₁ B₂).toLinearMap)
    (h_baseChange₀₂ : IsBaseChange A₂
      (IsScalarTower.toAlgHom A B B₂).toLinearMap)
    (h_finiteModel₀₁ : IsBaseChange A₁
      (IsScalarTower.toAlgHom A P P₁).toLinearMap)
    (h_finiteModel₁₂ : IsBaseChange A₂
      (IsScalarTower.toAlgHom A₁ P₁ P₂).toLinearMap)
    (h_finiteModel₀₂ : IsBaseChange A₂
      (IsScalarTower.toAlgHom A P P₂).toLinearMap)
    (x : RelativeDualizingModule.of A P B h_quasiFinite h_open) :
    baseChangeOf A₁ A₂ P₁ B₁ P₂ B₂ h_quasiFinite₁ h_quasiFinite₂
        h_open₁ h_open₂ h_baseChange₁₂ h_finiteModel₁₂
        (baseChangeOf A A₁ P B P₁ B₁ h_quasiFinite h_quasiFinite₁
          h_open h_open₁ h_baseChange₀₁ h_finiteModel₀₁ x) =
      baseChangeOf A A₂ P B P₂ B₂ h_quasiFinite h_quasiFinite₂
        h_open h_open₂ h_baseChange₀₂ h_finiteModel₀₂ x := sorry

end Algebra.RelativeDualizingModule
