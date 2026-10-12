/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.Comparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u v

/- Lemma 49.2.2: the two canonical maps from the relative dualizing module of a
common finite-open refinement to those of the original finite-open models are bijective. -/
@[stacks 0BT1] #check (Algebra.RelativeDualizingModule.commonRefinement_bijective :
  ∀ (A : Type u) (B₀ B₁ C B : Type v)
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
    (h_triangle₁ : (algebraMap C B).comp i₁.toRingHom = algebraMap B₁ B),
    Function.Bijective
        (Algebra.RelativeDualizingModule.comparison A B₀ C B h_quasiFinite
          h_open₀ h_openC i₀ h_triangle₀).hom ∧
      Function.Bijective
        (Algebra.RelativeDualizingModule.comparison A B₁ C B h_quasiFinite
          h_open₁ h_openC i₁ h_triangle₁).hom)
