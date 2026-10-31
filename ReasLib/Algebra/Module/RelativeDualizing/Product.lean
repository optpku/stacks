/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Finiteness.Prod
public import ReasLib.Algebra.Category.ModuleCat.Product
public import ReasLib.Algebra.Module.RelativeDualizing

@[expose] public section

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open scoped Algebra.DualModule TensorProduct TensorProduct.Right

universe u

namespace Algebra.Product

/-- The componentwise algebra structure on a product of two algebra extensions. -/
@[reducible]
def map
    (B' B C' C : Type u) [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [Algebra B' B] [Algebra C' C] :
    Algebra (B' × C') (B × C) :=
  (RingHom.prodMap (algebraMap B' B) (algebraMap C' C)).toAlgebra

scoped[Algebra.Product] attribute [instance] map

/-- The componentwise product algebra map acts coordinatewise. -/
theorem map_apply
    (B' B C' C : Type u) [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [Algebra B' B] [Algebra C' C] (x : B' × C') :
    algebraMap (B' × C') (B × C) x =
      (algebraMap B' B x.1, algebraMap C' C x.2) := by
  rfl

/-- Componentwise product algebra maps form a scalar tower over a common base. -/
scoped instance mapIsScalarTower
    (A B' B C' C : Type u)
    [CommRing A] [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A C'] [Algebra C' C] [Algebra A C] [IsScalarTower A C' C] :
    IsScalarTower A (B' × C') (B × C) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  apply Prod.ext
  · exact congrArg (fun f : A →+* B ↦ f a) (IsScalarTower.algebraMap_eq A B' B)
  · exact congrArg (fun f : A →+* C ↦ f a) (IsScalarTower.algebraMap_eq A C' C)

/-- The spectrum map of a componentwise product algebra is an open immersion when
the two component spectrum maps are open immersions. -/
scoped instance instIsOpenImmersionSpecMap
    (B' B C' C : Type u) [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [Algebra B' B] [Algebra C' C]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C)))] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (B' × C') (B × C)))) := by
  have h : coprodSpec B C ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (B' × C') (B × C))) =
      coprod.map (Spec.map (CommRingCat.ofHom (algebraMap B' B)))
        (Spec.map (CommRingCat.ofHom (algebraMap C' C))) ≫ coprodSpec B' C' := by
    apply coprod.hom_ext
    · simp only [coprodSpec_inl_assoc, coprod.inl_map_assoc,
        coprodSpec_inl, ← Spec.map_comp]
      congr 1
    · simp only [coprodSpec_inr_assoc, coprod.inr_map_assoc,
        coprodSpec_inr, ← Spec.map_comp]
      congr 1
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion (coprodSpec B C), h]
  infer_instance

end Algebra.Product

open scoped Algebra.Product

namespace Algebra.FiniteType.QuasiFinite

/-- The product of two finite-type quasi-finite algebras over a common base is
finite-type quasi-finite. -/
theorem prod
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (hB : Algebra.FiniteType.QuasiFinite A B)
    (hC : Algebra.FiniteType.QuasiFinite A C) :
    Algebra.FiniteType.QuasiFinite A (B × C) := by
  letI : Algebra.FiniteType A B := hB.1
  letI : Algebra.FiniteType A C := hC.1
  letI : Algebra.QuasiFinite A B := hB.2
  letI : Algebra.QuasiFinite A C := hC.2
  refine ⟨inferInstance, ⟨fun P hP ↦ ?_⟩⟩
  exact Module.Finite.equiv
    (_root_.TensorProduct.prodRight A P.ResidueField P.ResidueField B C).symm

end Algebra.FiniteType.QuasiFinite

namespace Algebra.RelativeDualizingModule

private theorem prod_smul
    (B' B C' C : Type u) [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [Algebra B' B] [Algebra C' C] (r : B' × C') (bc : B × C) :
    r • bc = (r.1 • bc.1, r.2 • bc.2) := by
  simp only [Algebra.smul_def, Algebra.Product.map_apply]
  rfl

private theorem dualProd_symm_smul
    (A B' C' : Type u) [CommRing A] [CommRing B'] [CommRing C']
    [Algebra A B'] [Algebra A C'] (r : B' × C') (φ : Module.Dual A (B' × C')) :
    (Module.dualProdDualEquivDual A B' C').symm (r • φ) =
      (r.1 • ((Module.dualProdDualEquivDual A B' C').symm φ).1,
        r.2 • ((Module.dualProdDualEquivDual A B' C').symm φ).2) := by
  apply Prod.ext
  · ext b
    change φ (r.1 * b, r.2 * 0) = φ (r.1 * b, 0)
    rw [mul_zero]
  · ext c
    change φ (r.1 * 0, r.2 * c) = φ (0, r.2 * c)
    rw [mul_zero]

private theorem prodTensor_smul
    (A B' B C' C : Type u)
    [CommRing A] [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A C'] [Algebra C' C]
    (F : Module.Dual A (B' × C') ⊗[B' × C'] (B × C) →+
      (Module.Dual A B' ⊗[B'] B) × (Module.Dual A C' ⊗[C'] C))
    (hF : ∀ (φ : Module.Dual A (B' × C')) (bc : B × C),
      F (φ ⊗ₜ[B' × C'] bc) =
        (((Module.dualProdDualEquivDual A B' C').symm φ).1 ⊗ₜ[B'] bc.1,
          ((Module.dualProdDualEquivDual A B' C').symm φ).2 ⊗ₜ[C'] bc.2)) :
    ∀ (r : B × C) (x : Module.Dual A (B' × C') ⊗[B' × C'] (B × C)),
      F (r • x) = (r.1 • (F x).1, r.2 • (F x).2) := by
  intro r x
  induction x using TensorProduct.induction_on with
  | zero => simp; rfl
  | tmul φ bc =>
    change F (φ ⊗ₜ[B' × C'] (r.1 * bc.1, r.2 * bc.2)) = _
    rw [hF, hF]
    rfl
  | add x y hx hy => simp [smul_add, hx, hy]

/-- The componentwise comparison from the chosen relative dualizing module of a
product algebra to the product of the two chosen relative dualizing modules. -/
def prodComparisonOf
    (A B' B C' C : Type u)
    [CommRing A] [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A C'] [Algebra C' C] [Algebra A C] [IsScalarTower A C' C]
    (hB : Algebra.FiniteType.QuasiFinite A B)
    (hC : Algebra.FiniteType.QuasiFinite A C)
    [Module.Finite A B'] [Module.Finite A C']
    [h_openB : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))]
    [h_openC : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C)))] :
    of A (B' × C') (B × C)
        (Algebra.FiniteType.QuasiFinite.prod hB hC)
        (inferInstance : IsOpenImmersion (Spec.map (CommRingCat.ofHom
          (algebraMap (B' × C') (B × C))))) ⟶
      CategoryTheory.ModuleCat.Product.combineObj B C
        (of A B' B hB h_openB)
        (of A C' C hC h_openC) :=
  let source := of A (B' × C') (B × C)
    (Algebra.FiniteType.QuasiFinite.prod hB hC)
    (inferInstance : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (B' × C') (B × C)))))
  let target := CategoryTheory.ModuleCat.Product.combineObj B C
    (of A B' B hB h_openB) (of A C' C hC h_openC)
  @ModuleCat.ofHom (B × C) _ (source : Type u) (target : Type u)
    source.isAddCommGroup source.isModule target.isAddCommGroup target.isModule
    ({ toFun :=
        TensorProduct.liftAddHom
          ({ toFun := fun φ ↦
              { toFun := fun bc ↦
                  let components := (Module.dualProdDualEquivDual A B' C').symm φ
                  (components.1 ⊗ₜ[B'] bc.1, components.2 ⊗ₜ[C'] bc.2)
                map_zero' := by simp
                map_add' := by
                  intro x y
                  simp [TensorProduct.tmul_add] }
             map_zero' := by ext bc <;> simp
             map_add' := by
               intro φ ψ
               ext bc <;> simp [LinearMap.add_comp, TensorProduct.add_tmul] } :
            Module.Dual A (B' × C') →+
              (B × C →+
                ((Module.Dual A B' ⊗[B'] B) ×
                  (Module.Dual A C' ⊗[C'] C))))
          (by
            intro r φ bc
            change
              (((Module.dualProdDualEquivDual A B' C').symm (r • φ)).1 ⊗ₜ[B'] bc.1,
                ((Module.dualProdDualEquivDual A B' C').symm (r • φ)).2 ⊗ₜ[C'] bc.2) =
              (((Module.dualProdDualEquivDual A B' C').symm φ).1 ⊗ₜ[B'] (r • bc).1,
                ((Module.dualProdDualEquivDual A B' C').symm φ).2 ⊗ₜ[C'] (r • bc).2)
            rw [dualProd_symm_smul, prod_smul]
            exact Prod.ext (TensorProduct.smul_tmul r.1 _ _)
              (TensorProduct.smul_tmul r.2 _ _))
       map_add' := by exact map_add _
       map_smul' := by
         change ∀ (r : B × C)
           (x : Module.Dual A (B' × C') ⊗[B' × C'] (B × C)),
           _ = (r.1 • _, r.2 • _)
         apply prodTensor_smul
         intro φ bc
         rfl } : source →ₗ[B × C] target)

/-- On a pure tensor, `prodComparisonOf` is the pair of tensors obtained from
the two components of the dual-of-product equivalence. -/
theorem prodComparisonOf_tmul
    (A B' B C' C : Type u)
    [CommRing A] [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A C'] [Algebra C' C] [Algebra A C] [IsScalarTower A C' C]
    (hB : Algebra.FiniteType.QuasiFinite A B)
    (hC : Algebra.FiniteType.QuasiFinite A C)
    [Module.Finite A B'] [Module.Finite A C']
    [h_openB : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))]
    [h_openC : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C)))]
    (φ : Module.Dual A (B' × C')) (b : B) (c : C) :
    prodComparisonOf A B' B C' C hB hC (φ ⊗ₜ[B' × C'] (b, c)) =
      (((Module.dualProdDualEquivDual A B' C').symm φ).1 ⊗ₜ[B'] b,
        ((Module.dualProdDualEquivDual A B' C').symm φ).2 ⊗ₜ[C'] c) := by
  rfl

/-- The product comparison map is bijective. -/
theorem prodComparisonOf_bijective
    (A B' B C' C : Type u)
    [CommRing A] [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A C'] [Algebra C' C] [Algebra A C] [IsScalarTower A C' C]
    (hB : Algebra.FiniteType.QuasiFinite A B)
    (hC : Algebra.FiniteType.QuasiFinite A C)
    [Module.Finite A B'] [Module.Finite A C']
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C)))] :
    Function.Bijective
      (prodComparisonOf A B' B C' C hB hC).hom := by
  let e := Module.dualProdDualEquivDual A B' C'
  let iB : Module.Dual A B' →ₗ[A] Module.Dual A (B' × C') :=
    e.toLinearMap.comp (LinearMap.inl A _ _)
  let iC : Module.Dual A C' →ₗ[A] Module.Dual A (B' × C') :=
    e.toLinearMap.comp (LinearMap.inr A _ _)
  have hiB (r : B') (φ : Module.Dual A B') :
      iB (r • φ) = ((r, 0) : B' × C') • iB φ := by
    apply LinearMap.ext
    intro x
    rfl
  have hiC (r : C') (φ : Module.Dual A C') :
      iC (r • φ) = ((0, r) : B' × C') • iC φ := by
    apply LinearMap.ext
    intro x
    rfl
  let gB : Module.Dual A B' →+ B →+
      Module.Dual A (B' × C') ⊗[B' × C'] (B × C) :=
    { toFun := fun φ ↦
        { toFun := fun b ↦ iB φ ⊗ₜ[B' × C'] (b, 0)
          map_zero' := by
            change iB φ ⊗ₜ[B' × C'] (0 : B × C) = 0
            rw [TensorProduct.tmul_zero]
          map_add' := by
            intro b b'
            simpa using TensorProduct.tmul_add (iB φ) (b, (0 : C)) (b', 0) }
      map_zero' := by ext b; simp
      map_add' := by intro φ ψ; ext b; simp [TensorProduct.add_tmul] }
  let gC : Module.Dual A C' →+ C →+
      Module.Dual A (B' × C') ⊗[B' × C'] (B × C) :=
    { toFun := fun φ ↦
        { toFun := fun c ↦ iC φ ⊗ₜ[B' × C'] (0, c)
          map_zero' := by
            change iC φ ⊗ₜ[B' × C'] (0 : B × C) = 0
            rw [TensorProduct.tmul_zero]
          map_add' := by
            intro c c'
            simpa using TensorProduct.tmul_add (iC φ) ((0 : B), c) (0, c') }
      map_zero' := by ext c; simp
      map_add' := by intro φ ψ; ext c; simp [TensorProduct.add_tmul] }
  have hgB (r : B') (φ : Module.Dual A B') (b : B) :
      gB (r • φ) b = gB φ (r • b) := by
    change (iB (r • φ)) ⊗ₜ[B' × C'] (b, 0) = iB φ ⊗ₜ[B' × C'] (r • b, 0)
    rw [hiB, TensorProduct.smul_tmul, prod_smul]
    simp
  have hgC (r : C') (φ : Module.Dual A C') (c : C) :
      gC (r • φ) c = gC φ (r • c) := by
    change (iC (r • φ)) ⊗ₜ[B' × C'] (0, c) = iC φ ⊗ₜ[B' × C'] (0, r • c)
    rw [hiC, TensorProduct.smul_tmul, prod_smul]
    simp
  let LB := TensorProduct.liftAddHom gB hgB
  let LC := TensorProduct.liftAddHom gC hgC
  let F : Module.Dual A (B' × C') ⊗[B' × C'] (B × C) →+
      (Module.Dual A B' ⊗[B'] B) × (Module.Dual A C' ⊗[C'] C) :=
    (prodComparisonOf A B' B C' C hB hC).hom.toAddMonoidHom
  let G := LB.coprod LC
  have hF (φ : Module.Dual A (B' × C')) (b : B) (c : C) :
      F (φ ⊗ₜ[B' × C'] (b, c)) =
        ((e.symm φ).1 ⊗ₜ[B'] b, (e.symm φ).2 ⊗ₜ[C'] c) :=
    prodComparisonOf_tmul A B' B C' C hB hC φ b c
  have hiB_proj (φ : Module.Dual A (B' × C')) :
      iB (e.symm φ).1 = ((1, 0) : B' × C') • φ := by
    apply LinearMap.ext
    intro x
    change φ (x.1, 0) + 0 = φ (1 * x.1, 0 * x.2)
    simp
  have hiC_proj (φ : Module.Dual A (B' × C')) :
      iC (e.symm φ).2 = ((0, 1) : B' × C') • φ := by
    apply LinearMap.ext
    intro x
    change 0 + φ (0, x.2) = φ (0 * x.1, 1 * x.2)
    simp
  have hleft : Function.LeftInverse G F := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul φ bc =>
      rw [hF]
      change LB ((e.symm φ).1 ⊗ₜ[B'] bc.1) +
        LC ((e.symm φ).2 ⊗ₜ[C'] bc.2) = _
      simp only [LB, LC, TensorProduct.liftAddHom_tmul]
      change iB (e.symm φ).1 ⊗ₜ[B' × C'] (bc.1, 0) +
        iC (e.symm φ).2 ⊗ₜ[B' × C'] (0, bc.2) = _
      rw [hiB_proj, hiC_proj, TensorProduct.smul_tmul, TensorProduct.smul_tmul,
        prod_smul, prod_smul]
      simp [← TensorProduct.tmul_add]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hLB (x : Module.Dual A B' ⊗[B'] B) : F (LB x) = (x, 0) := by
    induction x using TensorProduct.induction_on with
    | zero => simp; rfl
    | tmul φ b =>
      change F (iB φ ⊗ₜ[B' × C'] (b, 0)) = _
      rw [hF]
      simp [iB]
    | add x y hx hy => simp [hx, hy]
  have hLC (x : Module.Dual A C' ⊗[C'] C) : F (LC x) = (0, x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp; rfl
    | tmul φ c =>
      change F (iC φ ⊗ₜ[B' × C'] (0, c)) = _
      rw [hF]
      simp [iC]
    | add x y hx hy => simp [hx, hy]
  have hright : Function.RightInverse G F := by
    rintro ⟨x, y⟩
    change F (LB x + LC y) = (x, y)
    rw [F.map_add, hLB, hLC]
    simp
  exact ⟨hleft.injective, hright.surjective⟩

/-- The product comparison for chosen finite-open presentations is an isomorphism of
`B × C`-modules. -/
instance prodComparisonOf_isIso
    (A B' B C' C : Type u)
    [CommRing A] [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A C'] [Algebra C' C] [Algebra A C] [IsScalarTower A C' C]
    (hB : Algebra.FiniteType.QuasiFinite A B)
    (hC : Algebra.FiniteType.QuasiFinite A C)
    [Module.Finite A B'] [Module.Finite A C']
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C)))] :
    CategoryTheory.IsIso (prodComparisonOf A B' B C' C hB hC) := by
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (prodComparisonOf_bijective A B' B C' C hB hC)

end Algebra.RelativeDualizingModule
