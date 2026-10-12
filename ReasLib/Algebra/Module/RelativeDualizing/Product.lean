/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
      (algebraMap B' B x.1, algebraMap C' C x.2) := sorry

/-- Componentwise product algebra maps form a scalar tower over a common base. -/
scoped instance mapIsScalarTower
    (A B' B C' C : Type u)
    [CommRing A] [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A C'] [Algebra C' C] [Algebra A C] [IsScalarTower A C' C] :
    IsScalarTower A (B' × C') (B × C) := sorry

/-- The spectrum map of a componentwise product algebra is an open immersion when
the two component spectrum maps are open immersions. -/
scoped instance instIsOpenImmersionSpecMap
    (B' B C' C : Type u) [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [Algebra B' B] [Algebra C' C]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C)))] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (B' × C') (B × C)))) := sorry

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
    Algebra.FiniteType.QuasiFinite A (B × C) := sorry

end Algebra.FiniteType.QuasiFinite

namespace Algebra.RelativeDualizingModule

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
                map_zero' := sorry
                map_add' := sorry }
             map_zero' := sorry
             map_add' := sorry } :
            Module.Dual A (B' × C') →+
              (B × C →+
                ((Module.Dual A B' ⊗[B'] B) ×
                  (Module.Dual A C' ⊗[C'] C))))
          sorry
       map_add' := sorry
       map_smul' := sorry } : source →ₗ[B × C] target)

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
        ((Module.dualProdDualEquivDual A B' C').symm φ).2 ⊗ₜ[C'] c) := sorry

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
      (prodComparisonOf A B' B C' C hB hC).hom := sorry

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
    CategoryTheory.IsIso (prodComparisonOf A B' B C' C hB hC) := sorry

end Algebra.RelativeDualizingModule
