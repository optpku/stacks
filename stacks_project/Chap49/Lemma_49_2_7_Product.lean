/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.Product

@[expose] public section

open AlgebraicGeometry
open scoped Algebra.DualModule Algebra.Product TensorProduct TensorProduct.Right

universe u

#check (Algebra.Product.map :
  ∀ (B' B C' C : Type u) [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [Algebra B' B] [Algebra C' C], Algebra (B' × C') (B × C))

#check (Algebra.Product.map_apply :
  ∀ (B' B C' C : Type u) [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [Algebra B' B] [Algebra C' C] (x : B' × C'),
    algebraMap (B' × C') (B × C) x =
      (algebraMap B' B x.1, algebraMap C' C x.2))

#check (Algebra.Product.mapIsScalarTower :
  ∀ (A B' B C' C : Type u)
    [CommRing A] [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A C'] [Algebra C' C] [Algebra A C] [IsScalarTower A C' C],
    IsScalarTower A (B' × C') (B × C))

#check (Algebra.Product.instIsOpenImmersionSpecMap :
  ∀ (B' B C' C : Type u) [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [Algebra B' B] [Algebra C' C]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C)))],
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (B' × C') (B × C)))))

#check (Algebra.FiniteType.QuasiFinite.prod :
  ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C],
    Algebra.FiniteType.QuasiFinite A B →
      Algebra.FiniteType.QuasiFinite A C →
        Algebra.FiniteType.QuasiFinite A (B × C))

#check (Algebra.RelativeDualizingModule.prodComparisonOf :
  ∀ (A B' B C' C : Type u)
    [CommRing A] [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A C'] [Algebra C' C] [Algebra A C] [IsScalarTower A C' C]
    (hB : Algebra.FiniteType.QuasiFinite A B)
    (hC : Algebra.FiniteType.QuasiFinite A C)
    [Module.Finite A B'] [Module.Finite A C']
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C)))],
    Algebra.RelativeDualizingModule.of A (B' × C') (B × C)
      (Algebra.FiniteType.QuasiFinite.prod hB hC) inferInstance ⟶
      CategoryTheory.ModuleCat.Product.combineObj B C
        (Algebra.RelativeDualizingModule.of A B' B hB inferInstance)
        (Algebra.RelativeDualizingModule.of A C' C hC inferInstance))

#check (Algebra.RelativeDualizingModule.prodComparisonOf_tmul :
  ∀ (A B' B C' C : Type u)
    [CommRing A] [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A C'] [Algebra C' C] [Algebra A C] [IsScalarTower A C' C]
    (hB : Algebra.FiniteType.QuasiFinite A B)
    (hC : Algebra.FiniteType.QuasiFinite A C)
    [Module.Finite A B'] [Module.Finite A C']
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C)))]
    (φ : Module.Dual A (B' × C')) (b : B) (c : C),
    Algebra.RelativeDualizingModule.prodComparisonOf A B' B C' C hB hC
        (φ ⊗ₜ[B' × C'] (b, c)) =
      (((Module.dualProdDualEquivDual A B' C').symm φ).1 ⊗ₜ[B'] b,
        ((Module.dualProdDualEquivDual A B' C').symm φ).2 ⊗ₜ[C'] c))

#check (Algebra.RelativeDualizingModule.prodComparisonOf_bijective :
  ∀ (A B' B C' C : Type u)
    [CommRing A] [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A C'] [Algebra C' C] [Algebra A C] [IsScalarTower A C' C]
    (hB : Algebra.FiniteType.QuasiFinite A B)
    (hC : Algebra.FiniteType.QuasiFinite A C)
    [Module.Finite A B'] [Module.Finite A C']
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C)))],
    Function.Bijective
      (Algebra.RelativeDualizingModule.prodComparisonOf A B' B C' C hB hC).hom)

#check (Algebra.RelativeDualizingModule.prodComparisonOf_isIso :
  ∀ (A B' B C' C : Type u)
    [CommRing A] [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A C'] [Algebra C' C] [Algebra A C] [IsScalarTower A C' C]
    (hB : Algebra.FiniteType.QuasiFinite A B)
    (hC : Algebra.FiniteType.QuasiFinite A C)
    [Module.Finite A B'] [Module.Finite A C']
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C)))],
    CategoryTheory.IsIso
      (Algebra.RelativeDualizingModule.prodComparisonOf A B' B C' C hB hC))
