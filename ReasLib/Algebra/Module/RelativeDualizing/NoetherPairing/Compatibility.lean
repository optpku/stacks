/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.BaseChange
public import ReasLib.Algebra.Module.RelativeDualizing.NoetherPairing
public import ReasLib.Algebra.Module.RelativeDualizing.Product
public import ReasLib.RingTheory.Kaehler.NoetherDifferent.BaseChange
public import ReasLib.RingTheory.Kaehler.NoetherDifferent.Prod

@[expose] public section

open AlgebraicGeometry
open Algebra.FiniteType
open Algebra.FiniteType.QuasiFinite
open scoped Algebra.Product TensorProduct

universe u v

namespace Algebra.RelativeDualizingModule

/-- The Noether pairing is natural under a flat cartesian base change of
Noetherian rings and compatible finite open presentations. -/
theorem noetherPairing_baseChange
    (A A₁ : Type u) (B₀ B B₁₀ B₁ : Type v)
    [CommRing A] [CommRing A₁] [CommRing B₀] [CommRing B]
    [CommRing B₁₀] [CommRing B₁]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsNoetherianRing A₁] [IsNoetherianRing B₁]
    [Algebra A B₀] [Algebra B₀ B] [Algebra A B] [IsScalarTower A B₀ B]
    [Algebra A₁ B₁₀] [Algebra B₁₀ B₁] [Algebra A₁ B₁]
    [IsScalarTower A₁ B₁₀ B₁]
    [Algebra A A₁] [Algebra B₀ B₁₀] [Algebra B B₁]
    [Algebra A B₁₀] [IsScalarTower A B₀ B₁₀] [IsScalarTower A A₁ B₁₀]
    [Algebra A B₁] [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁]
    [Algebra B₀ B₁] [IsScalarTower B₀ B B₁] [IsScalarTower B₀ B₁₀ B₁]
    [Module.Flat A A₁]
    (h_quasiFinite : FiniteType.QuasiFinite A B)
    (h_quasiFinite₁ : FiniteType.QuasiFinite A₁ B₁)
    [Module.Finite A B₀] [Module.Finite A₁ B₁₀]
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₀ B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁₀ B₁))))
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B B₁).toLinearMap)
    (h_finiteModel : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B₀ B₁₀).toLinearMap)
    (omega : RelativeDualizingModule.of A B₀ B h_quasiFinite h_open)
    (xi : (KaehlerDifferential.ideal A B).annihilator) :
    noetherPairing A₁ B₁₀ B₁ h_quasiFinite₁ h_open₁
        (baseChangeOf A A₁ B₀ B B₁₀ B₁ h_quasiFinite h_quasiFinite₁
          h_open h_open₁ h_baseChange h_finiteModel omega)
        ⟨Algebra.TensorProduct.diagonalMap A A₁ B B₁ xi.1,
          KaehlerDifferential.diagonalMap_mem_annihilator A A₁ B B₁
            h_baseChange xi⟩ =
      algebraMap B B₁ (noetherPairing A B₀ B h_quasiFinite h_open omega xi) := sorry

/-- The first product projection commutes with the Noether pairing for chosen
finite open presentations of two quasi-finite algebras. -/
theorem noetherPairing_prod_fst
    (A B₁₀ B₁ B₂₀ B₂ : Type u)
    [CommRing A] [CommRing B₁₀] [CommRing B₁] [CommRing B₂₀] [CommRing B₂]
    [IsNoetherianRing A] [IsNoetherianRing B₁] [IsNoetherianRing B₂]
    [Algebra A B₁₀] [Algebra B₁₀ B₁] [Algebra A B₁] [IsScalarTower A B₁₀ B₁]
    [Algebra A B₂₀] [Algebra B₂₀ B₂] [Algebra A B₂] [IsScalarTower A B₂₀ B₂]
    (h_quasiFinite₁ : FiniteType.QuasiFinite A B₁)
    (h_quasiFinite₂ : FiniteType.QuasiFinite A B₂)
    [Module.Finite A B₁₀] [Module.Finite A B₂₀]
    [h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁₀ B₁)))]
    [h_open₂ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₂₀ B₂)))]
    (omega : RelativeDualizingModule.of A (B₁₀ × B₂₀) (B₁ × B₂)
      (prod h_quasiFinite₁ h_quasiFinite₂) inferInstance)
    (xi : (KaehlerDifferential.ideal A (B₁ × B₂)).annihilator) :
    noetherPairing A B₁₀ B₁ h_quasiFinite₁ h_open₁
        (prodComparisonOf A B₁₀ B₁ B₂₀ B₂ h_quasiFinite₁ h_quasiFinite₂ omega).1
        ⟨Algebra.TensorProduct.map (AlgHom.fst A B₁ B₂) (AlgHom.fst A B₁ B₂) xi.1,
          KaehlerDifferential.fst_mem_annihilator A B₁ B₂ xi⟩ =
      (noetherPairing A (B₁₀ × B₂₀) (B₁ × B₂)
        (prod h_quasiFinite₁ h_quasiFinite₂) inferInstance
        omega xi).1 := sorry

/-- The second product projection commutes with the Noether pairing for chosen
finite open presentations of two quasi-finite algebras. -/
theorem noetherPairing_prod_snd
    (A B₁₀ B₁ B₂₀ B₂ : Type u)
    [CommRing A] [CommRing B₁₀] [CommRing B₁] [CommRing B₂₀] [CommRing B₂]
    [IsNoetherianRing A] [IsNoetherianRing B₁] [IsNoetherianRing B₂]
    [Algebra A B₁₀] [Algebra B₁₀ B₁] [Algebra A B₁] [IsScalarTower A B₁₀ B₁]
    [Algebra A B₂₀] [Algebra B₂₀ B₂] [Algebra A B₂] [IsScalarTower A B₂₀ B₂]
    (h_quasiFinite₁ : FiniteType.QuasiFinite A B₁)
    (h_quasiFinite₂ : FiniteType.QuasiFinite A B₂)
    [Module.Finite A B₁₀] [Module.Finite A B₂₀]
    [h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁₀ B₁)))]
    [h_open₂ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₂₀ B₂)))]
    (omega : RelativeDualizingModule.of A (B₁₀ × B₂₀) (B₁ × B₂)
      (prod h_quasiFinite₁ h_quasiFinite₂) inferInstance)
    (xi : (KaehlerDifferential.ideal A (B₁ × B₂)).annihilator) :
    noetherPairing A B₂₀ B₂ h_quasiFinite₂ h_open₂
        (prodComparisonOf A B₁₀ B₁ B₂₀ B₂ h_quasiFinite₁ h_quasiFinite₂ omega).2
        ⟨Algebra.TensorProduct.map (AlgHom.snd A B₁ B₂) (AlgHom.snd A B₁ B₂) xi.1,
          KaehlerDifferential.snd_mem_annihilator A B₁ B₂ xi⟩ =
      (noetherPairing A (B₁₀ × B₂₀) (B₁ × B₂)
        (prod h_quasiFinite₁ h_quasiFinite₂) inferInstance
        omega xi).2 := sorry

end Algebra.RelativeDualizingModule
