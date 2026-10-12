/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor.CompositionHomotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Endomorphism
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy

/-!
# Composition of Differential Graded Bimodules

This leaf constructs the relative tensor product of composable differential graded bimodules.
The right module is the existing explicit relative tensor quotient.  Its left action is induced
by functoriality in the first tensor factor, and the two parenthesizations of a triple relative
tensor product are compared by explicit quotient maps.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open ComplexShape
open DifferentialGradedCategory
open HomologicalComplex
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedBimodule.Tensor

variable {R : Type u} [CommRing R]
variable {A B C : CochainDGAlgebra.{u, v} R}

/-- The left action of `A` on `N tensor_B N'`, obtained by tensoring the left action on `N`
with the identity of `N'`. -/
@[stacks 0BZ8 "left action underlying relative tensor composition"]
def composedLeftMulValue (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) (i p : ℤ) (a : A.X i) :
    (obj N.toRightModule N').X p →ₗ[R] (obj N.toRightModule N').X (i + p) :=
  ModuleCat.castLinearMap (congrArg (obj N.toRightModule N').X (add_comm p i))
    ((map N' ((LeftAction.ofBimodule N).toGradedHomValue i a)) p)

/-- The homogeneous left `A`-action on the relative tensor product of two bimodules. -/
@[stacks 0BZ8 "homogeneous left action on relative tensor composition"]
def composedLeftMul (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) (i p : ℤ) :
    A.X i →ₗ[R] (obj N.toRightModule N').X p →ₗ[R]
      (obj N.toRightModule N').X (i + p) where
  toFun := composedLeftMulValue N N' i p
  map_add' := sorry
  map_smul' := sorry

/-- The compatible left `A`-action on the right `C`-module `N tensor_B N'`. -/
@[stacks 0BZ8 "left action on relative tensor composition"]
def composedLeftAction (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) :
    LeftAction A (obj N.toRightModule N') where
  leftMul := composedLeftMul N N'
  left_assoc := sorry
  one_left := sorry
  comm_right := sorry
  d_leftMul := sorry

/-- The relative tensor product of composable differential graded bimodules, with underlying
right module exactly the explicit relative tensor quotient. -/
@[stacks 0BZ8 "relative tensor product of differential graded bimodules"]
def bimodule (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) :
    DifferentialGradedBimodule.{u, v, v, v} A C :=
  (composedLeftAction N N').toBimodule

/-- Restricting the composite bimodule to the right recovers the explicit relative tensor
right module. -/
@[stacks 0BZ8 "right-module carrier of the relative tensor bimodule", simp]
theorem bimodule_toRightModule (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) :
    (bimodule N N').toRightModule = obj N.toRightModule N' := sorry

/-- Degree `n` of the composite bimodule is the balancing quotient defining `N tensor_B N'`. -/
@[stacks 0BZ8 "graded component of the relative tensor bimodule", simp]
theorem bimodule_X (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) (n : ℤ) :
    (bimodule N N').X n = family N.toRightModule N' n := sorry

/-- The canonical object-level identification between the explicit balancing quotient and the
corresponding graded component of the composite bimodule.  This avoids exposing a carrier-level
type equality to downstream constructions. -/
@[stacks 0BZ8 "object-level carrier identification for the relative tensor bimodule"]
noncomputable def bimoduleXIso (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) (n : ℤ) :
    family N.toRightModule N' n ≅ (bimodule N N').X n :=
  eqToIso (by rfl)

/-- The forward carrier identification is definitionally the identity on elements. -/
@[stacks 0BZ8 "forward carrier identification for the relative tensor bimodule", simp]
theorem bimoduleXIso_hom_apply (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) (n : ℤ)
    (x : family N.toRightModule N' n) :
    ModuleCat.Hom.hom (bimoduleXIso N N' n).hom x = x := sorry

/-- The inverse carrier identification is definitionally the identity on elements. -/
@[stacks 0BZ8 "inverse carrier identification for the relative tensor bimodule", simp]
theorem bimoduleXIso_inv_apply (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) (n : ℤ)
    (x : (bimodule N N').X n) :
    ModuleCat.Hom.hom (bimoduleXIso N N' n).inv x = x := sorry

/-- The left action on a pure tensor is induced by the left action on its first factor. -/
@[stacks 0BZ8 "left action on pure tensors in a relative tensor bimodule"]
theorem bimodule_leftMul_tmul (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (i p q : ℤ) (a : A.X i) (x : N.X p) (y : N'.X q) :
    (bimodule N N').leftMul i (p + q) a
        (tmul N.toRightModule N' (p := p) (q := q) x y) =
      ModuleCat.Hom.hom (bimoduleXIso N N' (i + (p + q))).hom
        (cast
          (congrArg (fun n : ℤ ↦ (family N.toRightModule N' n : Type v))
            (add_assoc i p q))
          (tmul N.toRightModule N' (p := i + p) (q := q)
            (N.leftMul i p a x) y)) := sorry

/-- The iterated relative tensor product `(M tensor_A N) tensor_B N'`. -/
@[stacks 0BZ8 "iterated relative tensor product"]
abbrev iterated (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) :
    DifferentialGradedModule.{u, v} C :=
  obj (obj M N) N'

/-- The relative tensor product `M tensor_A (N tensor_B N')`. -/
@[stacks 0BZ8 "associated relative tensor product"]
abbrev associated (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) :
    DifferentialGradedModule.{u, v} C :=
  obj M (bimodule N N')

namespace Associator

/-- Degree reassociation for the forward relative-tensor associator. -/
theorem forwardDegree (r s p q n : ℤ)
    (hrs : r + s = p) (hpq : p + q = n) : r + (s + q) = n := sorry

/-- The forward associator on one homogeneous summand of the inner raw tensor product. -/
def forwardInnerComponent (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (n p q : ℤ) (hpq : p + q = n) (y : N'.X q)
    (r s : ℤ) (hrs : r + s = p) :
    DifferentialGradedModule.TensorProduct.baseTensor (R := R) (M.X r) (N.X s) ⟶
      family M (bimodule N N') n :=
  ModuleCat.TensorProduct.liftOfBilinear R
    (fun m x ↦
      cast
        (congrArg (fun k : ℤ ↦ (family M (bimodule N N') k : Type v))
          (forwardDegree r s p q n hrs hpq))
        (tmul M (bimodule N N') m (tmul N.toRightModule N' x y)))
    sorry sorry sorry sorry

/-- The forward associator on the inner unbalanced total tensor term. -/
def forwardInnerRaw (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (n p q : ℤ) (hpq : p + q = n) (y : N'.X q) :
    rawTerm M N p →ₗ[R] family M (bimodule N N') n :=
  (mapBifunctorDesc (K₁ := leftComplex M) (K₂ := rightComplex N)
    (F := DifferentialGradedModule.TensorProduct.baseBifunctor (R := R)) (c := up ℤ)
    (fun r s hrs ↦ forwardInnerComponent M N N' n p q hpq y r s hrs)).hom

/-- The inner `A`-balancing relations are killed by the forward associator. -/
theorem forwardInner_relations (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (n p q : ℤ) (hpq : p + q = n) (y : N'.X q) :
    relations M N p ≤
      LinearMap.ker (forwardInnerRaw M N N' n p q hpq y) := sorry

/-- The forward associator after imposing the inner `A`-balancing relations. -/
def forwardInner (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (n p q : ℤ) (hpq : p + q = n) (y : N'.X q) :
    family M N p →ₗ[R] family M (bimodule N N') n :=
  (relations M N p).liftQ (forwardInnerRaw M N N' n p q hpq y)
    (forwardInner_relations M N N' n p q hpq y)

/-- The forward associator on one homogeneous summand of the outer raw tensor product. -/
def forwardComponent (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (n p q : ℤ) (hpq : p + q = n) :
    DifferentialGradedModule.TensorProduct.baseTensor (R := R) ((obj M N).X p) (N'.X q) ⟶
      family M (bimodule N N') n :=
  ModuleCat.TensorProduct.liftOfBilinear R
    (fun x y ↦ forwardInner M N N' n p q hpq y x)
    sorry sorry sorry sorry

/-- The forward associator on the outer unbalanced total tensor term. -/
def forwardRaw (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) (n : ℤ) :
    rawTerm (obj M N) N' n →ₗ[R] family M (bimodule N N') n :=
  (mapBifunctorDesc (K₁ := leftComplex (obj M N)) (K₂ := rightComplex N')
    (F := DifferentialGradedModule.TensorProduct.baseBifunctor (R := R)) (c := up ℤ)
    (fun p q hpq ↦ forwardComponent M N N' n p q hpq)).hom

/-- The outer `B`-balancing relations are killed by the forward associator. -/
theorem forward_relations (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) (n : ℤ) :
    relations (obj M N) N' n ≤
      LinearMap.ker (forwardRaw M N N' n) := sorry

/-- The degreewise forward relative-tensor associator. -/
def forward (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) (n : ℤ) :
    (iterated M N N').X n →ₗ[R] (associated M N N').X n :=
  (relations (obj M N) N' n).liftQ (forwardRaw M N N' n)
    (forward_relations M N N' n)

/-- Degree reassociation for the inverse relative-tensor associator. -/
theorem backwardDegree (p q r s n : ℤ)
    (hpq : p + q = n) (hrs : r + s = q) : (p + r) + s = n := sorry

/-- The inverse associator on one homogeneous summand of the inner raw tensor product. -/
def backwardInnerComponent (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (n p q : ℤ) (hpq : p + q = n) (m : M.X p)
    (r s : ℤ) (hrs : r + s = q) :
    DifferentialGradedModule.TensorProduct.baseTensor (R := R) (N.X r) (N'.X s) ⟶
      family (obj M N) N' n :=
  ModuleCat.TensorProduct.liftOfBilinear R
    (fun x y ↦
      cast
        (congrArg (fun k : ℤ ↦ (family (obj M N) N' k : Type v))
          (backwardDegree p q r s n hpq hrs))
        (tmul (obj M N) N' (tmul M N m x) y))
    sorry sorry sorry sorry

/-- The inverse associator on the inner unbalanced tensor term. -/
def backwardInnerRaw (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (n p q : ℤ) (hpq : p + q = n) (m : M.X p) :
    rawTerm N.toRightModule N' q →ₗ[R] family (obj M N) N' n :=
  (mapBifunctorDesc (K₁ := leftComplex N.toRightModule) (K₂ := rightComplex N')
    (F := DifferentialGradedModule.TensorProduct.baseBifunctor (R := R)) (c := up ℤ)
    (fun r s hrs ↦ backwardInnerComponent M N N' n p q hpq m r s hrs)).hom

/-- The inner `B`-balancing relations are killed by the inverse associator. -/
theorem backwardInner_relations (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (n p q : ℤ) (hpq : p + q = n) (m : M.X p) :
    relations N.toRightModule N' q ≤
      LinearMap.ker (backwardInnerRaw M N N' n p q hpq m) := sorry

/-- The inverse associator after imposing the inner `B`-balancing relations. -/
def backwardInner (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (n p q : ℤ) (hpq : p + q = n) (m : M.X p) :
    family N.toRightModule N' q →ₗ[R] family (obj M N) N' n :=
  (relations N.toRightModule N' q).liftQ
    (backwardInnerRaw M N N' n p q hpq m)
    (backwardInner_relations M N N' n p q hpq m)

/-- The inverse associator on one homogeneous summand of the outer raw tensor product. -/
def backwardComponent (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (n p q : ℤ) (hpq : p + q = n) :
    DifferentialGradedModule.TensorProduct.baseTensor (R := R)
      (M.X p) ((bimodule N N').X q) ⟶ family (obj M N) N' n :=
  ModuleCat.TensorProduct.liftOfBilinear R
    (fun m z ↦ backwardInner M N N' n p q hpq m z)
    sorry sorry sorry sorry

/-- The inverse associator on the outer unbalanced total tensor term. -/
def backwardRaw (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) (n : ℤ) :
    rawTerm M (bimodule N N') n →ₗ[R] family (obj M N) N' n :=
  (mapBifunctorDesc (K₁ := leftComplex M) (K₂ := rightComplex (bimodule N N'))
    (F := DifferentialGradedModule.TensorProduct.baseBifunctor (R := R)) (c := up ℤ)
    (fun p q hpq ↦ backwardComponent M N N' n p q hpq)).hom

/-- The outer `A`-balancing relations are killed by the inverse associator. -/
theorem backward_relations (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) (n : ℤ) :
    relations M (bimodule N N') n ≤
      LinearMap.ker (backwardRaw M N N' n) := sorry

/-- The degreewise inverse relative-tensor associator. -/
def backward (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) (n : ℤ) :
    (associated M N N').X n →ₗ[R] (iterated M N N').X n :=
  (relations M (bimodule N N') n).liftQ (backwardRaw M N N' n)
    (backward_relations M N N' n)

/-- The forward associator as a morphism of right differential graded `C`-modules. -/
@[stacks 0BZ8 "forward morphism of the relative tensor associator"]
def hom (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) :
    iterated M N N' ⟶ associated M N N' where
  hom := forward M N N'
  comm_d := sorry
  comm_smul := sorry

/-- The inverse associator as a morphism of right differential graded `C`-modules. -/
@[stacks 0BZ8 "inverse morphism of the relative tensor associator"]
def inv (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) :
    associated M N N' ⟶ iterated M N N' where
  hom := backward M N N'
  comm_d := sorry
  comm_smul := sorry

end Associator

/-- Relative tensor products of differential graded modules and composable bimodules are
canonically associative. -/
@[stacks 0BZ8 "associativity of relative tensor products of differential graded bimodules"]
def associator (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) :
    iterated M N N' ≅ associated M N N' where
  hom := Associator.hom M N N'
  inv := Associator.inv M N N'
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward associator sends a nested pure tensor to the associated pure tensor. -/
@[stacks 0BZ8 "forward relative tensor associator on pure tensors"]
theorem associatorHom_tmul_tmul (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (p q r : ℤ) (m : M.X p) (x : N.X q) (y : N'.X r) :
    (associator M N N').hom.hom ((p + q) + r)
        (tmul (obj M N) N' (tmul M N m x) y) =
      cast
        (congrArg (fun n : ℤ ↦ ((associated M N N').X n : Type v))
          (add_assoc p q r).symm)
        (tmul M (bimodule N N') m (tmul N.toRightModule N' x y)) := sorry

/-- The inverse associator sends an associated pure tensor to the nested pure tensor. -/
@[stacks 0BZ8 "inverse relative tensor associator on pure tensors"]
theorem associatorInv_tmul_tmul (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (p q r : ℤ) (m : M.X p) (x : N.X q) (y : N'.X r) :
    (associator M N N').inv.hom (p + (q + r))
        (tmul M (bimodule N N') m (tmul N.toRightModule N' x y)) =
      cast
        (congrArg (fun n : ℤ ↦ ((iterated M N N').X n : Type v))
          (add_assoc p q r))
        (tmul (obj M N) N' (tmul M N m x) y) := sorry

namespace Associator

/-- The component of tensor associativity on closed degree-zero categories. -/
@[stacks 0BZ8 "component of tensor associativity on closed categories"]
def compApp (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (M : Comp R (DifferentialGradedModule.{u, v} A)) :
    ((dgFunctor N).mapComp ⋙ (dgFunctor N').mapComp).obj M ≅
      (dgFunctor (bimodule N N')).mapComp.obj M where
  hom := DifferentialGradedModule.homToCompHom (Associator.hom M.obj N N')
  inv := DifferentialGradedModule.homToCompHom (Associator.inv M.obj N N')
  hom_inv_id := sorry
  inv_hom_id := sorry

end Associator

/-- Tensor associativity as a natural isomorphism on closed degree-zero categories. -/
@[stacks 0BZ8 "tensor associativity on closed categories"]
def mapCompAssociator (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) :
    (dgFunctor N).mapComp ⋙ (dgFunctor N').mapComp ≅
      (dgFunctor (bimodule N N')).mapComp :=
  NatIso.ofComponents (Associator.compApp N N') (fun _ ↦ sorry)

/-- The forward component of the closed tensor associator is the explicit `compApp`. -/
@[simp, stacks 0BZ8 "forward component of closed tensor associativity"]
theorem mapCompAssociator_hom_app
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (M : Comp R (DifferentialGradedModule.{u, v} A)) :
    (mapCompAssociator N N').hom.app M = (Associator.compApp N N' M).hom := sorry

/-- The inverse component of the closed tensor associator is the inverse of `compApp`. -/
@[simp, stacks 0BZ8 "inverse component of closed tensor associativity"]
theorem mapCompAssociator_inv_app
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (M : Comp R (DifferentialGradedModule.{u, v} A)) :
    (mapCompAssociator N N').inv.app M = (Associator.compApp N N' M).inv := sorry

namespace Associator

/-- The component of tensor associativity on differential graded homotopy categories.  It is kept
under `Associator` because it is implementation data for `mapKAssociator`. -/
@[stacks 0BZ8 "component of tensor associativity on homotopy categories"]
def kApp (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (M : K R (DifferentialGradedModule.{u, v} A)) :
    ((dgFunctor N).mapK ⋙ (dgFunctor N').mapK).obj M ≅
      (dgFunctor (bimodule N N')).mapK.obj M where
  hom := (DifferentialGradedModule.homToCompHom
    (Associator.hom M.obj N N')).toHomotopyClass
  inv := (DifferentialGradedModule.homToCompHom
    (Associator.inv M.obj N N')).toHomotopyClass
  hom_inv_id := sorry
  inv_hom_id := sorry

end Associator

/-- Tensoring successively with two composable bimodules is naturally isomorphic on homotopy
categories to tensoring with their relative tensor product. -/
@[stacks 0BZ8 "tensor DG functor composition"]
def mapKAssociator (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) :
    (dgFunctor N).mapK ⋙ (dgFunctor N').mapK ≅
      (dgFunctor (bimodule N N')).mapK :=
  NatIso.ofComponents (Associator.kApp N N') (fun _ ↦ sorry)

/-- The forward component of the homotopy tensor associator is the explicit `kApp`. -/
@[simp, stacks 0BZ8 "forward component of homotopy tensor associativity"]
theorem mapKAssociator_hom_app
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (M : K R (DifferentialGradedModule.{u, v} A)) :
    (mapKAssociator N N').hom.app M = (Associator.kApp N N' M).hom := sorry

/-- The inverse component of the homotopy tensor associator is the inverse of `kApp`. -/
@[simp, stacks 0BZ8 "inverse component of homotopy tensor associativity"]
theorem mapKAssociator_inv_app
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (M : K R (DifferentialGradedModule.{u, v} A)) :
    (mapKAssociator N N').inv.app M = (Associator.kApp N N' M).inv := sorry

end DifferentialGradedBimodule.Tensor
