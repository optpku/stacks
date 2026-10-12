/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Algebra.DualModule TensorProduct TensorProduct.Right

universe u v

namespace Algebra.RelativeDualizingModule

/-- Restriction of functionals along a refinement of finite models induces the
canonical comparison between their chosen relative dualizing modules. -/
def comparison
    (A : Type u) (B₀ B₁ B : Type v)
    [CommRing A] [CommRing B₀] [CommRing B₁] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B₀] [Algebra B₀ B] [Algebra A B] [IsScalarTower A B₀ B]
    [Algebra A B₁] [Algebra B₁ B] [IsScalarTower A B₁ B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B₀] [Module.Finite A B₁]
    (h_open₀ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₀ B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁ B))))
    (i : B₀ →ₐ[A] B₁)
    (h_triangle : (algebraMap B₁ B).comp i.toRingHom = algebraMap B₀ B) :
    RelativeDualizingModule.of A B₁ B h_quasiFinite h_open₁ ⟶
      RelativeDualizingModule.of A B₀ B h_quasiFinite h_open₀ :=
  ModuleCat.ofHom
    ({ toFun :=
        TensorProduct.liftAddHom
          ({ toFun := fun f ↦
              { toFun := fun b ↦ (f.comp i.toLinearMap) ⊗ₜ[B₀] b
                map_zero' := sorry
                map_add' := sorry }
             map_zero' := sorry
             map_add' := sorry } :
            Module.Dual A B₁ →+ (B →+ (Module.Dual A B₀ ⊗[B₀] B)))
          sorry
       map_add' := sorry
       map_smul' := sorry } :
      RelativeDualizingModule.of A B₁ B h_quasiFinite h_open₁ →ₗ[B]
        RelativeDualizingModule.of A B₀ B h_quasiFinite h_open₀)

/-- The comparison map restricts the functional on every pure tensor. -/
theorem comparison_tmul
    (A : Type u) (B₀ B₁ B : Type v)
    [CommRing A] [CommRing B₀] [CommRing B₁] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B₀] [Algebra B₀ B] [Algebra A B] [IsScalarTower A B₀ B]
    [Algebra A B₁] [Algebra B₁ B] [IsScalarTower A B₁ B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B₀] [Module.Finite A B₁]
    (h_open₀ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₀ B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁ B))))
    (i : B₀ →ₐ[A] B₁)
    (h_triangle : (algebraMap B₁ B).comp i.toRingHom = algebraMap B₀ B)
    (f : Module.Dual A B₁) (b : B) :
    comparison A B₀ B₁ B h_quasiFinite h_open₀ h_open₁ i h_triangle
        (f ⊗ₜ[B₁] b) =
      (f.comp i.toLinearMap) ⊗ₜ[B₀] b := sorry

/-- The canonical comparison along a refinement of finite open models is bijective. -/
theorem comparison_bijective
    (A : Type u) (B₀ B₁ B : Type v)
    [CommRing A] [CommRing B₀] [CommRing B₁] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B₀] [Algebra B₀ B] [Algebra A B] [IsScalarTower A B₀ B]
    [Algebra A B₁] [Algebra B₁ B] [IsScalarTower A B₁ B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B₀] [Module.Finite A B₁]
    (h_open₀ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₀ B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁ B))))
    (i : B₀ →ₐ[A] B₁)
    (h_triangle : (algebraMap B₁ B).comp i.toRingHom = algebraMap B₀ B) :
    Function.Bijective
      (comparison A B₀ B₁ B h_quasiFinite h_open₀ h_open₁ i h_triangle).hom := sorry

/-- The comparison along a refinement is a categorical isomorphism. -/
instance comparison_isIso
    (A : Type u) (B₀ B₁ B : Type v)
    [CommRing A] [CommRing B₀] [CommRing B₁] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B₀] [Algebra B₀ B] [Algebra A B] [IsScalarTower A B₀ B]
    [Algebra A B₁] [Algebra B₁ B] [IsScalarTower A B₁ B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B₀] [Module.Finite A B₁]
    (h_open₀ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₀ B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁ B))))
    (i : B₀ →ₐ[A] B₁)
    (h_triangle : (algebraMap B₁ B).comp i.toRingHom = algebraMap B₀ B) :
    IsIso (comparison A B₀ B₁ B h_quasiFinite h_open₀ h_open₁ i h_triangle) := sorry

/-- Comparison along the identity refinement is the identity morphism. -/
theorem comparison_id
    (A : Type u) (B₀ B : Type v)
    [CommRing A] [CommRing B₀] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B₀] [Algebra B₀ B] [Algebra A B] [IsScalarTower A B₀ B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B₀]
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₀ B))))
    (h_triangle : (algebraMap B₀ B).comp (AlgHom.id A B₀).toRingHom =
      algebraMap B₀ B) :
    comparison A B₀ B₀ B h_quasiFinite h_open h_open (AlgHom.id A B₀) h_triangle =
      𝟙 (RelativeDualizingModule.of A B₀ B h_quasiFinite h_open) := sorry

/-- Comparisons along composable refinements compose in the contravariant direction. -/
theorem comparison_comp
    (A : Type u) (B₀ B₁ B₂ B : Type v)
    [CommRing A] [CommRing B₀] [CommRing B₁] [CommRing B₂] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B₀] [Algebra B₀ B] [Algebra A B] [IsScalarTower A B₀ B]
    [Algebra A B₁] [Algebra B₁ B] [IsScalarTower A B₁ B]
    [Algebra A B₂] [Algebra B₂ B] [IsScalarTower A B₂ B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B₀] [Module.Finite A B₁] [Module.Finite A B₂]
    (h_open₀ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₀ B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁ B))))
    (h_open₂ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₂ B))))
    (i₀₁ : B₀ →ₐ[A] B₁) (i₁₂ : B₁ →ₐ[A] B₂)
    (h_triangle₀₁ : (algebraMap B₁ B).comp i₀₁.toRingHom = algebraMap B₀ B)
    (h_triangle₁₂ : (algebraMap B₂ B).comp i₁₂.toRingHom = algebraMap B₁ B)
    (h_triangle₀₂ : (algebraMap B₂ B).comp (i₁₂.comp i₀₁).toRingHom =
      algebraMap B₀ B) :
    comparison A B₀ B₂ B h_quasiFinite h_open₀ h_open₂
        (i₁₂.comp i₀₁) h_triangle₀₂ =
      comparison A B₁ B₂ B h_quasiFinite h_open₁ h_open₂ i₁₂ h_triangle₁₂ ≫
        comparison A B₀ B₁ B h_quasiFinite h_open₀ h_open₁ i₀₁ h_triangle₀₁ := sorry

/-- A common finite open refinement induces bijective comparison maps to both
of the original finite open models. -/
theorem commonRefinement_bijective
    (A : Type u) (B₀ B₁ C B : Type v)
    [CommRing A] [CommRing B₀] [CommRing B₁] [CommRing C] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B₀] [Algebra B₀ B] [Algebra A B] [IsScalarTower A B₀ B]
    [Algebra A B₁] [Algebra B₁ B] [IsScalarTower A B₁ B]
    [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B₀] [Module.Finite A B₁] [Module.Finite A C]
    (h_open₀ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₀ B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁ B))))
    (h_openC : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C B))))
    (i₀ : B₀ →ₐ[A] C) (i₁ : B₁ →ₐ[A] C)
    (h_triangle₀ : (algebraMap C B).comp i₀.toRingHom = algebraMap B₀ B)
    (h_triangle₁ : (algebraMap C B).comp i₁.toRingHom = algebraMap B₁ B) :
    Function.Bijective
        (comparison A B₀ C B h_quasiFinite h_open₀ h_openC i₀ h_triangle₀).hom ∧
      Function.Bijective
        (comparison A B₁ C B h_quasiFinite h_open₁ h_openC i₁ h_triangle₁).hom := sorry

end Algebra.RelativeDualizingModule
