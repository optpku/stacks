/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.ShortExact
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits
open scoped Module.Determinant TensorProduct

universe u v

/- Lemma 50.18.1 (1): a finite-free two-term diagram over a short exact row has canonical
exterior-power comparison maps. -/
@[stacks 0FL8] #check (@CategoryTheory.ShortComplex.ShortExact.exteriorComparison :
  ∀ {R : Type u} [CommRing R] {S : ShortComplex (ModuleCat.{v} R)}
    {N : ModuleCat.{v} R} (_ : S.ShortExact) (dL : N ⟶ S.X₂) (dM : N ⟶ S.X₃)
    (_ : dL ≫ S.g = dM) [Module.Free R N] [Module.Finite R N]
    [Module.Free R S.X₃] [Module.Finite R S.X₃]
    (_ : Module.finrank R N = Module.finrank R S.X₃) (p : ℕ),
    (cokernel dL).exteriorPower p →ₗ[R]
      S.X₁.exteriorPower p ⊗[R] (det[R](N) →ₗ[R] det[R](S.X₃)))

/- Lemma 50.18.1 (2): the degree-zero comparison is the discriminant of the two-term
complex. -/
@[stacks 0FL8] #check (@CategoryTheory.ShortComplex.ShortExact.exteriorComparison_zero :
  ∀ {R : Type u} [CommRing R] {S : ShortComplex (ModuleCat.{v} R)}
    {N : ModuleCat.{v} R} (hS : S.ShortExact) (dL : N ⟶ S.X₂) (dM : N ⟶ S.X₃)
    (hcomm : dL ≫ S.g = dM) [Module.Free R N] [Module.Finite R N]
    [Module.Free R S.X₃] [Module.Finite R S.X₃]
    (hRank : Module.finrank R N = Module.finrank R S.X₃),
    CategoryTheory.ShortComplex.ShortExact.exteriorComparison hS dL dM hcomm hRank 0
        (ModuleCat.exteriorPower.oneLinear (cokernel dL) (1 : R)) =
      ModuleCat.exteriorPower.oneLinear S.X₁ (1 : R) ⊗ₜ[R]
        ModuleCat.twoTermDiscriminant dM hRank)

/- Lemma 50.18.1 (3): the comparison maps commute with left exterior multiplication. -/
@[stacks 0FL8] #check (@CategoryTheory.ShortComplex.ShortExact.exteriorComparison_wedge :
  ∀ {R : Type u} [CommRing R] {S : ShortComplex (ModuleCat.{v} R)}
    {N : ModuleCat.{v} R} (hS : S.ShortExact) (dL : N ⟶ S.X₂) (dM : N ⟶ S.X₃)
    (hcomm : dL ≫ S.g = dM) [Module.Free R N] [Module.Finite R N]
    [Module.Free R S.X₃] [Module.Finite R S.X₃]
    (hRank : Module.finrank R N = Module.finrank R S.X₃)
    (q p : ℕ) (ω : S.X₁.exteriorPower q) (η : (cokernel dL).exteriorPower p),
    CategoryTheory.ShortComplex.ShortExact.exteriorComparison hS dL dM hcomm hRank (q + p)
        (ModuleCat.exteriorPower.mul (cokernel dL) q p
          (ModuleCat.exteriorPower.map (S.f ≫ cokernel.π dL) q ω ⊗ₜ[R] η)) =
      TensorProduct.map (ModuleCat.exteriorPower.mul S.X₁ q p).hom LinearMap.id
        ((TensorProduct.assoc R (S.X₁.exteriorPower q) (S.X₁.exteriorPower p)
          (det[R](N) →ₗ[R] det[R](S.X₃))).symm
            (ω ⊗ₜ[R] CategoryTheory.ShortComplex.ShortExact.exteriorComparison
              hS dL dM hcomm hRank p η)))

/- Lemma 50.18.1 (4): the induced composite is tensor multiplication by the
discriminant. -/
@[stacks 0FL8] #check (@CategoryTheory.ShortComplex.ShortExact.exteriorComparison_comp :
  ∀ {R : Type u} [CommRing R] {S : ShortComplex (ModuleCat.{v} R)}
    {N : ModuleCat.{v} R} (hS : S.ShortExact) (dL : N ⟶ S.X₂) (dM : N ⟶ S.X₃)
    (hcomm : dL ≫ S.g = dM) [Module.Free R N] [Module.Finite R N]
    [Module.Free R S.X₃] [Module.Finite R S.X₃]
    (hRank : Module.finrank R N = Module.finrank R S.X₃) (p : ℕ),
    (CategoryTheory.ShortComplex.ShortExact.exteriorComparison hS dL dM hcomm hRank p).comp
        (ModuleCat.exteriorPower.map (S.f ≫ cokernel.π dL) p).hom =
      (TensorProduct.mk R (S.X₁.exteriorPower p)
        (det[R](N) →ₗ[R] det[R](S.X₃))).flip
          (ModuleCat.twoTermDiscriminant dM hRank))
