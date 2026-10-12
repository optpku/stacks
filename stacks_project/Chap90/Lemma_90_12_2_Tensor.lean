/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation
public import stacks_project.Chap90.Definition_90_19_2_DualNumber
public import stacks_project.Chap90.Lemma_90_10_4_Along
public import stacks_project.Chap90.Lemma_90_11_6_Tensor
public import stacks_project.Chap90.Lemma_90_12_2_SquareZero
public import stacks_project.Chap90.Remark_90_6_3_PredeformationFunctor
public import stacks_project.Chap90.Remark_90_10_3
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass

/-!
# Tangent-space module structure and tensor comparison

If `F-bar` satisfies Schlessinger's (H2), the fibrewise isomorphism-class value
`F-bar(k[ε])` carries a natural `k`-vector space structure, and the values
`F-bar(k[V])` compare with `F-bar(k[ε]) ⊗[k] V`.
-/

@[expose] public section

noncomputable section

open CategoryTheory hiding Linear
open CategoryTheory.Limits
open ArtinianLocalAlgCat
open FGModuleCat
open scoped TensorProduct

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- Evaluation of a functor on finitely generated square-zero extensions `k[V]`. -/
def fgEval (F : ArtinianLocalAlgCat Λ k ⥤ Type v) : FGModuleCat.{u} k ⥤ Type v :=
  squareZeroFunctor Λ k ⋙ F

/-- Evaluation of `fgEval` at `V` is `F.obj (squareZero Λ k V)`. -/
theorem fgEval_obj (F : ArtinianLocalAlgCat Λ k ⥤ Type v) (V : FGModuleCat.{u} k) :
    (fgEval F).obj V = F.obj (squareZero Λ k V) :=
  rfl

/-- `fgEval` acts on morphisms by the underlying action of `F`. -/
theorem fgEval_map (F : ArtinianLocalAlgCat Λ k ⥤ Type v) {V W : FGModuleCat.{u} k}
    (f : V ⟶ W) :
    (fgEval F).map f = F.map ((squareZeroFunctor Λ k).map f) :=
  rfl

variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

/-- The fibre over `k` of a predeformation category has a unique isomorphism class. -/
instance instUnique_fiberIsoClass_residue [IsPredeformationCategory p] :
    Unique ((fiberIsoClassFunctor p).obj (residue Λ k)) where
  default :=
    Quotient.mk'' (Classical.choice IsPredeformationCategory.nonempty_residueFiber)
  uniq := sorry

/-- The associated isomorphism-class functor of a predeformation category is a
predeformation functor. -/
instance instIsPredeformationFunctor_fiberIsoClassFunctor [IsPredeformationCategory p] :
    IsPredeformationFunctor (fiberIsoClassFunctor p) where
  unique_residue := ⟨inferInstance⟩

/-- Matching pair of tangent vectors over the dual-number pullback, using that both
map to the unique residue class. -/
def fiberDualTangentAddPair [IsPredeformationCategory p]
    (x y : (fiberIsoClassFunctor p).obj (dualNumber Λ k)) :
    Types.PullbackObj
      ((fiberIsoClassFunctor p).map (toResidue (dualNumber Λ k)))
      ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k)) :=
  ⟨(x, y), sorry⟩

/-- Addition on `F-bar(k[ε])` via the (H2) comparison along `k[ε] ×_k k[ε]` and the sum map. -/
def addFiberDualTangent [IsPredeformationCategory p]
    [HasSchlessingerH2 (fiberIsoClassFunctor p)]
    (x y : (fiberIsoClassFunctor p).obj (dualNumber Λ k)) :
    (fiberIsoClassFunctor p).obj (dualNumber Λ k) :=
  (fiberIsoClassFunctor p).map dualNumberSum
    ((Equiv.ofBijective
        (pullbackObjMap_subtype (fiberIsoClassFunctor p)
          (dualNumberPullbackFst (dualNumber Λ k))
          (dualNumberPullbackSnd (dualNumber Λ k))
          (toResidue (dualNumber Λ k))
          (dualNumberToResidue Λ k)
          (isPullback_dualNumberPullback (dualNumber Λ k)))
        (HasSchlessingerH2.bijective_pullbackObjMap
          (toResidue (dualNumber Λ k))
          (dualNumberPullbackFst (dualNumber Λ k))
          (dualNumberPullbackSnd (dualNumber Λ k))
          (isPullback_dualNumberPullback (dualNumber Λ k)))).symm
      (fiberDualTangentAddPair p x y))

/-- Scalar multiplication on `F-bar(k[ε])` by dual-number scaling of `ε`. -/
def smulFiberDualTangent [IsPredeformationCategory p]
    (r : k) (x : (fiberIsoClassFunctor p).obj (dualNumber Λ k)) :
    (fiberIsoClassFunctor p).obj (dualNumber Λ k) :=
  (fiberIsoClassFunctor p).map (dualNumberSMul Λ k r) x

/-- Zero of `F-bar(k[ε])`, as the image of the unique residue class along `k ⟶ k[ε]`. -/
def zeroFiberDualTangent [IsPredeformationCategory p] :
    (fiberIsoClassFunctor p).obj (dualNumber Λ k) :=
  (fiberIsoClassFunctor p).map (residueToDualNumber Λ k) default

/-- Addition on `F-bar(k[ε])`. -/
instance instAdd_fiberDualTangent [IsPredeformationCategory p]
    [HasSchlessingerH2 (fiberIsoClassFunctor p)] :
    Add ((fiberIsoClassFunctor p).obj (dualNumber Λ k)) where
  add := addFiberDualTangent p

/-- Zero on `F-bar(k[ε])`. -/
instance instZero_fiberDualTangent [IsPredeformationCategory p] :
    Zero ((fiberIsoClassFunctor p).obj (dualNumber Λ k)) where
  zero := zeroFiberDualTangent p

/-- Negation on `F-bar(k[ε])`, as scaling by `-1`. -/
instance instNeg_fiberDualTangent [IsPredeformationCategory p] :
    Neg ((fiberIsoClassFunctor p).obj (dualNumber Λ k)) where
  neg x := smulFiberDualTangent p (-1) x

/-- Scalar multiplication on `F-bar(k[ε])`. -/
instance instSMul_fiberDualTangent [IsPredeformationCategory p] :
    SMul k ((fiberIsoClassFunctor p).obj (dualNumber Λ k)) where
  smul := smulFiberDualTangent p

/-- The additive group structure on `F-bar(k[ε])`. -/
instance instAddCommGroup_fiberDualTangent [IsPredeformationCategory p]
    [HasSchlessingerH2 (fiberIsoClassFunctor p)] :
    AddCommGroup ((fiberIsoClassFunctor p).obj (dualNumber Λ k)) where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  neg_add_cancel := sorry
  zsmul := zsmulRec
  add_comm := sorry

/-- The `k`-module structure on `F-bar(k[ε])`. -/
instance instModule_fiberDualTangent [IsPredeformationCategory p]
    [HasSchlessingerH2 (fiberIsoClassFunctor p)] :
    Module k ((fiberIsoClassFunctor p).obj (dualNumber Λ k)) where
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

variable (G : ArtinianLocalAlgCat Λ k ⥤ Type v)

/-- A functor to types with a unique value at `k` has a unique value at `k`. -/
instance instUnique_obj_residue [IsPredeformationFunctor G] :
    Unique (G.obj (residue Λ k)) :=
  Classical.choice IsPredeformationFunctor.unique_residue

/-- Matching pair of values over `A ×_k k[V]`, using uniqueness at the residue field. -/
def objSquareZeroAddPair [IsPredeformationFunctor G] [HasSchlessingerH2 G]
    {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (x y : G.obj (squareZero Λ k V)) :
    Types.PullbackObj
      (G.map (toResidue (squareZero Λ k V)))
      (G.map (squareZeroToResidue Λ k V)) :=
  ⟨(x, y), sorry⟩

/-- Addition on `G.obj (squareZero Λ k V)` via (H2) along `k[V] ×_k k[V]`. -/
def addObjSquareZero [IsPredeformationFunctor G] [HasSchlessingerH2 G]
    {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (x y : G.obj (squareZero Λ k V)) : G.obj (squareZero Λ k V) :=
  G.map (squareZeroSum V)
    ((Equiv.ofBijective
        (pullbackObjMap_subtype G
          (squareZeroPullbackFst (squareZero Λ k V) V)
          (squareZeroPullbackSnd (squareZero Λ k V) V)
          (toResidue (squareZero Λ k V))
          (squareZeroToResidue Λ k V)
          (isPullback_squareZeroPullback (squareZero Λ k V) V))
        (hasSchlessingerH2_squareZero G
          (toResidue (squareZero Λ k V))
          (squareZeroPullbackFst (squareZero Λ k V) V)
          (squareZeroPullbackSnd (squareZero Λ k V) V)
          (isPullback_squareZeroPullback (squareZero Λ k V) V))).symm
      (objSquareZeroAddPair G x y))

/-- Scalar multiplication on `G.obj (squareZero Λ k V)`. -/
def smulObjSquareZero {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (r : k) (x : G.obj (squareZero Λ k V)) : G.obj (squareZero Λ k V) :=
  G.map (squareZeroMap (LinearMap.lsmul k V r)) x

/-- Zero of `G.obj (squareZero Λ k V)`. -/
def zeroObjSquareZero [IsPredeformationFunctor G]
    {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V] :
    G.obj (squareZero Λ k V) :=
  G.map (residueToSquareZero V) default

/-- Addition on values at `k[V]`. -/
instance instAdd_obj_squareZero [IsPredeformationFunctor G] [HasSchlessingerH2 G]
    (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    Add (G.obj (squareZero Λ k V)) where
  add := addObjSquareZero G

/-- Zero on values at `k[V]`. -/
instance instZero_obj_squareZero [IsPredeformationFunctor G]
    (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    Zero (G.obj (squareZero Λ k V)) where
  zero := zeroObjSquareZero G

/-- Negation on values at `k[V]`. -/
instance instNeg_obj_squareZero [IsPredeformationFunctor G]
    (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    Neg (G.obj (squareZero Λ k V)) where
  neg x := smulObjSquareZero G (-1) x

/-- Scalar multiplication on values at `k[V]`. -/
instance instSMul_obj_squareZero (V : Type u) [AddCommGroup V] [Module k V]
    [Module.Finite k V] : SMul k (G.obj (squareZero Λ k V)) where
  smul := smulObjSquareZero G

/-- The additive group structure on `G(k[V])`. -/
instance instAddCommGroup_obj_squareZero [IsPredeformationFunctor G] [HasSchlessingerH2 G]
    (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    AddCommGroup (G.obj (squareZero Λ k V)) where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  neg_add_cancel := sorry
  zsmul := zsmulRec
  add_comm := sorry

/-- The `k`-module structure on `G(k[V])`. -/
instance instModule_obj_squareZero [IsPredeformationFunctor G] [HasSchlessingerH2 G]
    (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    Module k (G.obj (squareZero Λ k V)) where
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- Transport of tangent vectors along `k[ε] ≅ k[k]`. -/
def fiberDualTangentEquiv_squareZero [IsPredeformationCategory p] :
    (fiberIsoClassFunctor p).obj (dualNumber Λ k) ≃
      (fgEval (fiberIsoClassFunctor p)).obj (of k k) where
  toFun := (fiberIsoClassFunctor p).map (dualNumberIsoSquareZero Λ k).hom
  invFun := (fiberIsoClassFunctor p).map (dualNumberIsoSquareZero Λ k).inv
  left_inv := sorry
  right_inv := sorry

variable [IsPredeformationCategory p] [HasSchlessingerH2 (fiberIsoClassFunctor p)]
variable (V : FGModuleCat.{u} k)

/-- The bilinear map `(x, v) ↦ F-bar(k[span{v}])(x)` underlying the tensor comparison. -/
def fiberDualTangentTensorBilin :
    (fiberIsoClassFunctor p).obj (dualNumber Λ k) →ₗ[k]
      V →ₗ[k] (fiberIsoClassFunctor p).obj (squareZero Λ k V) :=
  LinearMap.mk₂ k
    (fun x v ↦
      (fiberIsoClassFunctor p).map
        ((dualNumberIsoSquareZero Λ k).hom ≫ squareZeroMap (LinearMap.toSpanSingleton k V v)) x)
    sorry sorry sorry sorry

/-- The canonical `k`-linear comparison `F-bar(k[ε]) ⊗[k] V →ₗ[k] F-bar(k[V])`. -/
def fiberDualTangentTensor :
    (fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] V →ₗ[k]
      (fiberIsoClassFunctor p).obj (squareZero Λ k V) :=
  TensorProduct.lift (fiberDualTangentTensorBilin p V)

/-- On pure tensors, `fiberDualTangentTensor` sends `x ⊗ₜ v` to the image of `x` under
the map induced by `spanSingleton v`. -/
theorem fiberDualTangentTensor_tmul
    (x : (fiberIsoClassFunctor p).obj (dualNumber Λ k)) (v : V) :
    fiberDualTangentTensor p V (x ⊗ₜ v) =
      (fiberIsoClassFunctor p).map
        ((dualNumberIsoSquareZero Λ k).hom ≫
          squareZeroMap (LinearMap.toSpanSingleton k V v)) x := sorry

/-- `fiberDualTangentTensor` is the lift of `fiberDualTangentTensorBilin`. -/
theorem fiberDualTangentTensor_spec :
    fiberDualTangentTensor p V = TensorProduct.lift (fiberDualTangentTensorBilin p V) := sorry

/-- Type-level form of `fiberDualTangentTensor`, for a finite `k`-module `W`. -/
def fiberDualTangentTensor_of (W : Type u) [AddCommGroup W] [Module k W] [Module.Finite k W] :
    (fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] W →ₗ[k]
      (fiberIsoClassFunctor p).obj (squareZero Λ k W) :=
  fiberDualTangentTensor p (of k W)

/-- `fiberDualTangentTensor_of` is `fiberDualTangentTensor` at `FGModuleCat.of k W`. -/
theorem fiberDualTangentTensor_of_eq (W : Type u) [AddCommGroup W] [Module k W]
    [Module.Finite k W] :
    fiberDualTangentTensor_of p W = fiberDualTangentTensor p (of k W) := sorry

/-- The comparison `F-bar(k[ε]) ⊗[k] V → F-bar(k[V])` is natural in the finite-dimensional
`k`-vector space `V`. -/
theorem fiberDualTangentTensor_naturality {W : FGModuleCat.{u} k} (f : V ⟶ W)
    (x : (fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] V) :
    (fiberIsoClassFunctor p).map ((squareZeroFunctor Λ k).map f)
        (fiberDualTangentTensor p V x) =
      fiberDualTangentTensor p W (TensorProduct.map LinearMap.id f.hom.hom x) := sorry

end CategoryTheory.Functor
