/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.Comparison

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Algebra.DualModule TensorProduct TensorProduct.Right

universe u v

/- Refinement of finite models induces a contravariant comparison morphism. -/
#check (Algebra.RelativeDualizingModule.comparison :
  ∀ (A : Type u) (B₀ B₁ B : Type v)
    [CommRing A] [CommRing B₀] [CommRing B₁] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B₀] [Algebra B₀ B] [Algebra A B] [IsScalarTower A B₀ B]
    [Algebra A B₁] [Algebra B₁ B] [IsScalarTower A B₁ B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B₀] [Module.Finite A B₁]
    (h_open₀ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₀ B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁ B))))
    (i : B₀ →ₐ[A] B₁)
    (h_triangle : (algebraMap B₁ B).comp i.toRingHom = algebraMap B₀ B),
    Algebra.RelativeDualizingModule.of A B₁ B h_quasiFinite h_open₁ ⟶
      Algebra.RelativeDualizingModule.of A B₀ B h_quasiFinite h_open₀)

/- The comparison morphism has the expected value on pure tensors. -/
#check (Algebra.RelativeDualizingModule.comparison_tmul :
  ∀ (A : Type u) (B₀ B₁ B : Type v)
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
    (f : Module.Dual A B₁) (b : B),
    Algebra.RelativeDualizingModule.comparison A B₀ B₁ B h_quasiFinite
        h_open₀ h_open₁ i h_triangle (f ⊗ₜ[B₁] b) =
      (f.comp i.toLinearMap) ⊗ₜ[B₀] b)

/- Comparison along a finite open refinement is bijective. -/
#check (Algebra.RelativeDualizingModule.comparison_bijective :
  ∀ (A : Type u) (B₀ B₁ B : Type v)
    [CommRing A] [CommRing B₀] [CommRing B₁] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B₀] [Algebra B₀ B] [Algebra A B] [IsScalarTower A B₀ B]
    [Algebra A B₁] [Algebra B₁ B] [IsScalarTower A B₁ B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B₀] [Module.Finite A B₁]
    (h_open₀ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₀ B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁ B))))
    (i : B₀ →ₐ[A] B₁)
    (h_triangle : (algebraMap B₁ B).comp i.toRingHom = algebraMap B₀ B),
    Function.Bijective
      (Algebra.RelativeDualizingModule.comparison A B₀ B₁ B h_quasiFinite
        h_open₀ h_open₁ i h_triangle).hom)

/- Comparison along a finite open refinement is a categorical isomorphism. -/
#check (Algebra.RelativeDualizingModule.comparison_isIso :
  ∀ (A : Type u) (B₀ B₁ B : Type v)
    [CommRing A] [CommRing B₀] [CommRing B₁] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B₀] [Algebra B₀ B] [Algebra A B] [IsScalarTower A B₀ B]
    [Algebra A B₁] [Algebra B₁ B] [IsScalarTower A B₁ B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B₀] [Module.Finite A B₁]
    (h_open₀ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₀ B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁ B))))
    (i : B₀ →ₐ[A] B₁)
    (h_triangle : (algebraMap B₁ B).comp i.toRingHom = algebraMap B₀ B),
    IsIso (Algebra.RelativeDualizingModule.comparison A B₀ B₁ B h_quasiFinite
      h_open₀ h_open₁ i h_triangle))

/- Comparison along the identity refinement is the identity. -/
#check (Algebra.RelativeDualizingModule.comparison_id :
  ∀ (A : Type u) (B₀ B : Type v)
    [CommRing A] [CommRing B₀] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B₀] [Algebra B₀ B] [Algebra A B] [IsScalarTower A B₀ B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B₀]
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₀ B))))
    (h_triangle : (algebraMap B₀ B).comp (AlgHom.id A B₀).toRingHom =
      algebraMap B₀ B),
    Algebra.RelativeDualizingModule.comparison A B₀ B₀ B h_quasiFinite
        h_open h_open (AlgHom.id A B₀) h_triangle =
      𝟙 (Algebra.RelativeDualizingModule.of A B₀ B h_quasiFinite h_open))

/- Comparisons compose in the contravariant direction. -/
#check (Algebra.RelativeDualizingModule.comparison_comp :
  ∀ (A : Type u) (B₀ B₁ B₂ B : Type v)
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
      algebraMap B₀ B),
    Algebra.RelativeDualizingModule.comparison A B₀ B₂ B h_quasiFinite
        h_open₀ h_open₂ (i₁₂.comp i₀₁) h_triangle₀₂ =
      Algebra.RelativeDualizingModule.comparison A B₁ B₂ B h_quasiFinite
          h_open₁ h_open₂ i₁₂ h_triangle₁₂ ≫
        Algebra.RelativeDualizingModule.comparison A B₀ B₁ B h_quasiFinite
          h_open₀ h_open₁ i₀₁ h_triangle₀₁)
