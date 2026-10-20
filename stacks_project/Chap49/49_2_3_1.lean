module

public import ReasLib.Algebra.Module.RelativeDualizing.BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped Algebra.DualModule TensorProduct TensorProduct.Right

universe u v

/- 49.2.3.1: for a base change `A → A₁` with `B₁` the base change of `B`, and
compatible chosen finite models `B'` and `B₁'`, there is a base-change map
`ω_{B/A} ⟶ ω_{B₁/A₁}`. -/
@[stacks 0BVB] #check (Algebra.RelativeDualizingModule.baseChangeOf :
  ∀ (A A₁ : Type u) (B' B B₁' B₁ : Type v)
    [CommRing A] [CommRing A₁] [CommRing B'] [CommRing B]
    [CommRing B₁'] [CommRing B₁]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsNoetherianRing A₁] [IsNoetherianRing B₁]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A₁ B₁'] [Algebra B₁' B₁] [Algebra A₁ B₁]
    [IsScalarTower A₁ B₁' B₁]
    [Algebra A A₁] [Algebra B' B₁'] [Algebra B B₁]
    [Algebra A B₁'] [IsScalarTower A B' B₁'] [IsScalarTower A A₁ B₁']
    [Algebra A B₁] [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁]
    [Algebra B' B₁] [IsScalarTower B' B B₁] [IsScalarTower B' B₁' B₁]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    (h_quasiFinite₁ : Algebra.FiniteType.QuasiFinite A₁ B₁)
    [Module.Finite A B'] [Module.Finite A₁ B₁']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁' B₁))))
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B B₁).toLinearMap)
    (h_finiteModel : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B' B₁').toLinearMap),
    Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open
      →ₛₗ[algebraMap B B₁]
        Algebra.RelativeDualizingModule.of A₁ B₁' B₁ h_quasiFinite₁ h_open₁)
