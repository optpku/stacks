/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import ReasLib.LinearAlgebra.TensorProduct.RightModule

/-!
# Descent Data for Modules

This file owns the fixed-carrier descent datum for modules along a map of
commutative rings. The three maps on a triple tensor product are constructed
from the supplied equivalence by tensor functoriality, associativity, and
symmetry.
-/

@[expose] public section

open scoped TensorProduct TensorProduct.Right

noncomputable section

namespace Module

universe u v w x y z

namespace DescentDatum

variable {R : Type u} {A : Type v} {N : Type w} {N' : Type x}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup N] [Module R N] [Module A N]
variable [IsScalarTower R A N] [SMulCommClass R A N]
variable [AddCommGroup N'] [Module R N'] [Module A N']
variable [IsScalarTower R A N'] [SMulCommClass R A N']

/-- Extend a descent equivalence over tensor positions `0` and `1`, leaving
the final copy of `A` fixed. -/
noncomputable def extend01
    (e : N ⊗[R] A ≃ₗ[A ⊗[R] A] A ⊗[R] N) :
    (N ⊗[R] A) ⊗[R] A →ₗ[(A ⊗[R] A) ⊗[R] A]
      (A ⊗[R] N) ⊗[R] A :=
  let f : (N ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] N) ⊗[R] A :=
    TensorProduct.map (e.toLinearMap.restrictScalars R)
      (LinearMap.id : A →ₗ[R] A)
  { toFun := f
    map_add' := f.map_add
    map_smul' := sorry }

/-- The `01` extension applies the descent equivalence to the first outer
tensor factor. -/
theorem extend01_tmul (e : N ⊗[R] A ≃ₗ[A ⊗[R] A] A ⊗[R] N)
    (n : N) (a b : A) :
    extend01 e ((n ⊗ₜ[R] a) ⊗ₜ[R] b) = e (n ⊗ₜ[R] a) ⊗ₜ[R] b := sorry

/-- Extend a descent equivalence over tensor positions `1` and `2`, using
the tensor-product associator to leave the first copy of `A` fixed. -/
noncomputable def extend12
    (e : N ⊗[R] A ≃ₗ[A ⊗[R] A] A ⊗[R] N) :
    (A ⊗[R] N) ⊗[R] A →ₗ[(A ⊗[R] A) ⊗[R] A]
      (A ⊗[R] A) ⊗[R] N :=
  let middle : A ⊗[R] (N ⊗[R] A) →ₗ[R] A ⊗[R] (A ⊗[R] N) :=
    TensorProduct.map (LinearMap.id : A →ₗ[R] A)
      (e.toLinearMap.restrictScalars R)
  let f : (A ⊗[R] N) ⊗[R] A →ₗ[R] (A ⊗[R] A) ⊗[R] N :=
    (TensorProduct.assoc R A A N).symm.toLinearMap.comp <|
      middle.comp (TensorProduct.assoc R A N A).toLinearMap
  { toFun := f
    map_add' := f.map_add
    map_smul' := sorry }

/-- On a pure triple tensor, the `12` extension applies the descent
equivalence to the final two factors. -/
theorem extend12_tmul (e : N ⊗[R] A ≃ₗ[A ⊗[R] A] A ⊗[R] N)
    (a b : A) (n : N) :
    extend12 e ((a ⊗ₜ[R] n) ⊗ₜ[R] b) =
      (TensorProduct.assoc R A A N).symm (a ⊗ₜ[R] e (n ⊗ₜ[R] b)) := sorry

/-- Extend a descent equivalence over tensor positions `0` and `2`. The
middle and final scalar factors are exchanged before applying the supplied
equivalence, and exchanged back afterwards. -/
noncomputable def extend02
    (e : N ⊗[R] A ≃ₗ[A ⊗[R] A] A ⊗[R] N) :
    (N ⊗[R] A) ⊗[R] A →ₗ[(A ⊗[R] A) ⊗[R] A]
      (A ⊗[R] A) ⊗[R] N :=
  let swapScalars : N ⊗[R] (A ⊗[R] A) →ₗ[R] N ⊗[R] (A ⊗[R] A) :=
    TensorProduct.map (LinearMap.id : N →ₗ[R] N)
      (TensorProduct.comm R A A).toLinearMap
  let applyEquiv : (N ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] N) ⊗[R] A :=
    TensorProduct.map (e.toLinearMap.restrictScalars R)
      (LinearMap.id : A →ₗ[R] A)
  let swapModule : A ⊗[R] (N ⊗[R] A) →ₗ[R] A ⊗[R] (A ⊗[R] N) :=
    TensorProduct.map (LinearMap.id : A →ₗ[R] A)
      (TensorProduct.comm R N A).toLinearMap
  let f : (N ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] A) ⊗[R] N :=
    (TensorProduct.assoc R A A N).symm.toLinearMap.comp <|
      swapModule.comp <| (TensorProduct.assoc R A N A).toLinearMap.comp <|
        applyEquiv.comp <| (TensorProduct.assoc R N A A).symm.toLinearMap.comp <|
          swapScalars.comp (TensorProduct.assoc R N A A).toLinearMap
  { toFun := f
    map_add' := f.map_add
    map_smul' := sorry }

/-- On a pure triple tensor, the `02` extension applies the descent
equivalence after transposing the two scalar factors. -/
theorem extend02_tmul (e : N ⊗[R] A ≃ₗ[A ⊗[R] A] A ⊗[R] N)
    (n : N) (a b : A) :
    extend02 e ((n ⊗ₜ[R] a) ⊗ₜ[R] b) =
      (TensorProduct.assoc R A A N).symm
        (TensorProduct.map (LinearMap.id : A →ₗ[R] A)
          (TensorProduct.comm R N A).toLinearMap
          ((TensorProduct.assoc R A N A) (e (n ⊗ₜ[R] b) ⊗ₜ[R] a))) := sorry

/-- The cocycle condition for a module descent equivalence: its consecutive
`01` and `12` extensions agree with its `02` extension. -/
def CocycleCondition
    (e : N ⊗[R] A ≃ₗ[A ⊗[R] A] A ⊗[R] N) : Prop :=
  (extend12 e).comp (extend01 e) = extend02 e

/-- The named cocycle condition is exactly equality of the two canonical
maps on the triple tensor product. -/
theorem cocycleCondition_iff
    (e : N ⊗[R] A ≃ₗ[A ⊗[R] A] A ⊗[R] N) :
    CocycleCondition e ↔ (extend12 e).comp (extend01 e) = extend02 e := sorry

end DescentDatum

/-- An `A`-module descent datum along `R → A`: an `A ⊗[R] A`-linear
equivalence together with its cocycle law on the triple tensor product. -/
structure DescentDatum (R : Type u) (A : Type v) (N : Type w)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] [SMulCommClass R A N] where
  /-- The comparison between extension on the right and extension on the left. -/
  equiv : N ⊗[R] A ≃ₗ[A ⊗[R] A] A ⊗[R] N
  /-- Compatibility of the three pullbacks to the triple tensor product. -/
  cocycle : DescentDatum.CocycleCondition equiv

namespace DescentDatum

variable {R : Type u} {A : Type v} {N : Type w} {N' : Type x}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup N] [Module R N] [Module A N]
variable [IsScalarTower R A N] [SMulCommClass R A N]
variable [AddCommGroup N'] [Module R N'] [Module A N']
variable [IsScalarTower R A N'] [SMulCommClass R A N']

/-- Construct a module descent datum from its explicit equivalence and
cocycle proof. -/
def ofEquiv (e : N ⊗[R] A ≃ₗ[A ⊗[R] A] A ⊗[R] N)
    (h : CocycleCondition e) : DescentDatum R A N :=
  { equiv := e
    cocycle := h }

/-- Reading the equivalence from `ofEquiv` returns the supplied equivalence. -/
theorem ofEquiv_equiv (e : N ⊗[R] A ≃ₗ[A ⊗[R] A] A ⊗[R] N)
    (h : CocycleCondition e) : (ofEquiv e h).equiv = e := sorry

/-- The cocycle of a descent datum evaluated at an element of the triple
tensor product. -/
theorem cocycle_apply (D : DescentDatum R A N) (x : (N ⊗[R] A) ⊗[R] A) :
    extend12 D.equiv (extend01 D.equiv x) = extend02 D.equiv x := sorry

/-- Tensor an `A`-linear map with the identity on the right, as an
`A ⊗[R] A`-linear map. -/
def mapFirst (f : N →ₗ[A] N') :
    N ⊗[R] A →ₗ[A ⊗[R] A] N' ⊗[R] A :=
  let g : N ⊗[R] A →ₗ[R] N' ⊗[R] A :=
    TensorProduct.map (f.restrictScalars R) (LinearMap.id : A →ₗ[R] A)
  { toFun := g
    map_add' := g.map_add
    map_smul' := sorry }

/-- `mapFirst` acts on pure tensors by applying the map to the first factor. -/
theorem mapFirst_tmul (f : N →ₗ[A] N') (n : N) (a : A) :
    mapFirst f (n ⊗ₜ[R] a) = f n ⊗ₜ[R] a := sorry

/-- Tensor an `A`-linear map with the identity on the left, as an
`A ⊗[R] A`-linear map. -/
def mapSecond (f : N →ₗ[A] N') :
    A ⊗[R] N →ₗ[A ⊗[R] A] A ⊗[R] N' :=
  let g : A ⊗[R] N →ₗ[R] A ⊗[R] N' :=
    TensorProduct.map (LinearMap.id : A →ₗ[R] A) (f.restrictScalars R)
  { toFun := g
    map_add' := g.map_add
    map_smul' := sorry }

/-- `mapSecond` acts on pure tensors by applying the map to the second factor. -/
theorem mapSecond_tmul (f : N →ₗ[A] N') (a : A) (n : N) :
    mapSecond f (a ⊗ₜ[R] n) = a ⊗ₜ[R] f n := sorry

/-- A morphism of module descent data is an `A`-linear map commuting with
the two descent equivalences. -/
structure Hom (D : DescentDatum R A N) (D' : DescentDatum R A N') where
  /-- The underlying map of `A`-modules. -/
  hom : N →ₗ[A] N'
  /-- Compatibility with the descent equivalences. -/
  comm : D'.equiv.toLinearMap.comp (mapFirst hom) =
    (mapSecond hom).comp D.equiv.toLinearMap

namespace Hom

variable {D : DescentDatum R A N} {D' : DescentDatum R A N'}

/-- Construct a morphism of descent data from an `A`-linear map and its
compatibility proof. -/
def ofLinearMap (f : N →ₗ[A] N')
    (h : D'.equiv.toLinearMap.comp (mapFirst f) =
      (mapSecond f).comp D.equiv.toLinearMap) : Hom D D' :=
  { hom := f
    comm := h }

/-- Two morphisms of descent data are equal when their underlying linear
maps are equal. -/
theorem ext {f g : Hom D D'} (h : f.hom = g.hom) : f = g := sorry

/-- The identity morphism of a module descent datum. -/
def id (D : DescentDatum R A N) : Hom D D where
  hom := LinearMap.id
  comm := sorry

/-- The underlying linear map of an identity morphism is the identity. -/
theorem id_hom (D : DescentDatum R A N) : (id D).hom = LinearMap.id := sorry

/-- Compose two morphisms of module descent data. -/
def comp {N'' : Type y} [AddCommGroup N''] [Module R N''] [Module A N'']
    [IsScalarTower R A N''] [SMulCommClass R A N'']
    {D'' : DescentDatum R A N''} (f : Hom D D') (g : Hom D' D'') : Hom D D'' where
  hom := g.hom.comp f.hom
  comm := sorry

/-- The underlying linear map of a composite is the composite of the
underlying linear maps. -/
theorem comp_hom {N'' : Type y} [AddCommGroup N''] [Module R N''] [Module A N'']
    [IsScalarTower R A N''] [SMulCommClass R A N'']
    {D'' : DescentDatum R A N''} (f : Hom D D') (g : Hom D' D'') :
    (comp f g).hom = g.hom.comp f.hom := sorry

/-- Left identity for morphisms of module descent data. -/
theorem id_comp (f : Hom D D') : comp (id D) f = f := sorry

/-- Right identity for morphisms of module descent data. -/
theorem comp_id (f : Hom D D') : comp f (id D') = f := sorry

/-- Associativity of composition for morphisms of module descent data. -/
theorem assoc {N'' : Type y} {N''' : Type z}
    [AddCommGroup N''] [Module R N''] [Module A N'']
    [IsScalarTower R A N''] [SMulCommClass R A N'']
    [AddCommGroup N'''] [Module R N'''] [Module A N''']
    [IsScalarTower R A N'''] [SMulCommClass R A N''']
    {D'' : DescentDatum R A N''} {D''' : DescentDatum R A N'''}
    (f : Hom D D') (g : Hom D' D'') (h : Hom D'' D''') :
    comp (comp f g) h = comp f (comp g h) := sorry

end Hom

end DescentDatum

end Module
