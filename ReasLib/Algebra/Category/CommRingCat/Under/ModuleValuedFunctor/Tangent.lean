/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModulePair
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct ZeroObject

universe u

namespace ModuleValuedFunctor

variable {A : CommRingCat.{u}}

/-- The semilinear map underlying the transition map of a module-valued functor. -/
noncomputable def mapSemilinear (F : ModuleValuedFunctor.{u, u} A)
    {B B' : Under A} (f : B ⟶ B') :
    F.obj B →ₛₗ[f.right.hom] F.obj B' :=
  (ModuleCat.semilinearMapAddEquiv f.right.hom (F.obj B) (F.obj B')).symm (F.map f)

/-- The semilinear transition map agrees pointwise with the original transition map. -/
theorem mapSemilinear_apply (F : ModuleValuedFunctor.{u, u} A) {B B' : Under A}
    (f : B ⟶ B') (x : F.obj B) : F.mapSemilinear f x = F.map f x := sorry

/-- The value of `F` on `B[N]`, restricted along `B ⟶ B[N]`. -/
noncomputable abbrev squareZeroValue (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) : ModuleCat.{u} B.right :=
  (ModuleCat.restrictScalars (ModulePair.inclusion B N).right.hom).obj
    (F.obj (ModulePair.squareZero B N))

/-- The restricted square-zero value has the same underlying additive group as `F(B[N])`. -/
theorem squareZeroValue_carrier (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) :
    (F.squareZeroValue B N : Type u) = F.obj (ModulePair.squareZero B N) := sorry

/-- The augmentation on `F(B[N])` is linear over `B`. -/
theorem tangentAugmentation_map_smul (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) (b : B.right) (x : F.squareZeroValue B N) :
    F.map (ModulePair.projection B N) (b • x) =
      b • F.map (ModulePair.projection B N) x := sorry

/-- The augmentation on `F(B[N])`, viewed as a `B`-linear map. -/
noncomputable def tangentAugmentation (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) : F.squareZeroValue B N ⟶ F.obj B :=
  ModuleCat.ofHom (R := B.right) (X := F.squareZeroValue B N) (Y := F.obj B) {
    toFun := fun x : F.squareZeroValue B N => F.map (ModulePair.projection B N) x
    map_add' := (F.map (ModulePair.projection B N)).hom.map_add
    map_smul' := tangentAugmentation_map_smul F B N }

/-- The tangent augmentation acts by `F` on the square-zero projection. -/
theorem tangentAugmentation_apply (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) (x : F.squareZeroValue B N) :
    F.tangentAugmentation B N x = F.map (ModulePair.projection B N) x := sorry

/-- The section of the tangent augmentation induced by `B ⟶ B[N]`. -/
noncomputable def tangentSection (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) : F.obj B ⟶ F.squareZeroValue B N :=
  F.map (ModulePair.inclusion B N)

/-- The tangent section acts by `F` on the square-zero inclusion. -/
theorem tangentSection_apply (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) (x : F.obj B) :
    F.tangentSection B N x = F.map (ModulePair.inclusion B N) x := sorry

/-- The tangent section is a section of the tangent augmentation. -/
theorem tangentSection_comp_augmentation (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) :
    F.tangentSection B N ≫ F.tangentAugmentation B N = 𝟙 (F.obj B) := sorry

/-- The chosen splitting of the tangent augmentation. -/
noncomputable def tangentSplitEpi (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) : SplitEpi (F.tangentAugmentation B N) where
  section_ := F.tangentSection B N
  id := F.tangentSection_comp_augmentation B N

/-- The tangent augmentation is canonically a split epimorphism. -/
noncomputable def tangentAugmentationIsSplitEpi (F : ModuleValuedFunctor.{u, u} A)
    (B : Under A) (N : ModuleCat.{u} B.right) : IsSplitEpi (F.tangentAugmentation B N) :=
  IsSplitEpi.mk' (F.tangentSplitEpi B N)

/-- The tangent module `TF(B, N)`, defined as the categorical kernel of the augmentation. -/
noncomputable def tangentObj (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) : ModuleCat.{u} B.right :=
  (ModuleCat.kernelCone (F.tangentAugmentation B N)).pt

/-- The canonical inclusion of the tangent kernel into the restricted square-zero value. -/
noncomputable def tangentι (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) : F.tangentObj B N ⟶ F.squareZeroValue B N :=
  (ModuleCat.kernelCone (F.tangentAugmentation B N)).ι

/-- The tangent inclusion is killed by the augmentation. -/
theorem tangent_ι_comp (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) :
    F.tangentι B N ≫ F.tangentAugmentation B N = 0 := sorry

/-- A pair morphism sends tangent vectors into the target tangent kernel. -/
theorem tangentMap_mem (F : ModuleValuedFunctor.{u, u} A) {B B' : Under A}
    {N : ModuleCat.{u} B.right} {N' : ModuleCat.{u} B'.right}
    (f : ModulePair.Map B N B' N') (x : F.tangentObj B N) :
    F.map (ModulePair.map f) x.1 ∈ (F.tangentAugmentation B' N').hom.ker := sorry

/-- The underlying function on tangent kernels induced by a pair morphism. -/
noncomputable def tangentMapFun (F : ModuleValuedFunctor.{u, u} A) {B B' : Under A}
    {N : ModuleCat.{u} B.right} {N' : ModuleCat.{u} B'.right}
    (f : ModulePair.Map B N B' N') (x : F.tangentObj B N) : F.tangentObj B' N' :=
  ⟨F.map (ModulePair.map f) x.1, F.tangentMap_mem f x⟩

/-- The tangent map preserves addition. -/
theorem tangentMap_add (F : ModuleValuedFunctor.{u, u} A) {B B' : Under A}
    {N : ModuleCat.{u} B.right} {N' : ModuleCat.{u} B'.right}
    (f : ModulePair.Map B N B' N') (x y : F.tangentObj B N) :
    F.tangentMapFun f (x + y) = F.tangentMapFun f x + F.tangentMapFun f y := sorry

/-- The tangent map is semilinear over the base algebra map. -/
theorem tangentMap_smul (F : ModuleValuedFunctor.{u, u} A) {B B' : Under A}
    {N : ModuleCat.{u} B.right} {N' : ModuleCat.{u} B'.right}
    (f : ModulePair.Map B N B' N') (b : B.right) (x : F.tangentObj B N) :
    F.tangentMapFun f (b • x) = f.base.right.hom b • F.tangentMapFun f x := sorry

/-- The semilinear tangent map induced by a morphism of algebra-module pairs. -/
noncomputable def tangentMap (F : ModuleValuedFunctor.{u, u} A) {B B' : Under A}
    {N : ModuleCat.{u} B.right} {N' : ModuleCat.{u} B'.right}
    (f : ModulePair.Map B N B' N') :
    F.tangentObj B N →ₛₗ[f.base.right.hom] F.tangentObj B' N' where
  toFun := F.tangentMapFun f
  map_add' := F.tangentMap_add f
  map_smul' := F.tangentMap_smul f

/-- Tangent transport along the identity pair morphism is the identity. -/
theorem tangentMap_id (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) (x : F.tangentObj B N) :
    F.tangentMap (ModulePair.Map.id B N) x = x := sorry

/-- Tangent transport respects composition of pair morphisms. -/
theorem tangentMap_comp (F : ModuleValuedFunctor.{u, u} A) {B B' B'' : Under A}
    {N : ModuleCat.{u} B.right} {N' : ModuleCat.{u} B'.right}
    {N'' : ModuleCat.{u} B''.right} (f : ModulePair.Map B N B' N')
    (g : ModulePair.Map B' N' B'' N'') (x : F.tangentObj B N) :
    F.tangentMap (ModulePair.Map.comp f g) x = F.tangentMap g (F.tangentMap f x) := sorry

/-- The tangent construction as a functor on algebra-module pairs. -/
noncomputable def tangent (F : ModuleValuedFunctor.{u, u} A) : ModulePairFunctor A where
  obj B N := F.tangentObj B N
  map f := F.tangentMap f
  map_id B N := F.tangentMap_id B N
  map_comp f g := F.tangentMap_comp f g

/-- The tangent pair functor evaluates to the kernel-defined tangent module. -/
theorem tangent_obj (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) : F.tangent.obj B N = F.tangentObj B N := sorry

/-- The canonical decomposition of `F(B[N])` into `F(B)` and its tangent kernel. -/
noncomputable def tangentDecomposition (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) :
    F.squareZeroValue B N ≅ F.obj B ⊞ F.tangentObj B N :=
  -- Local instance justification (proof-local temporary data): the Mathlib splitting constructor requires the explicitly constructed split-epi fact as a temporary typeclass argument.
  letI := F.tangentAugmentationIsSplitEpi B N
  biprod.uniqueUpToIso (F.tangentObj B N) (F.obj B)
      (isBilimitBinaryBiconeOfIsSplitEpiOfKernel
        (ModuleCat.kernelIsLimit (F.tangentAugmentation B N))) ≪≫
    biprod.braiding (F.tangentObj B N) (F.obj B)

/-- The first projection of the tangent decomposition is the augmentation `F(B[N]) ⟶ F(B)`. -/
theorem tangentDecomposition_hom_fst (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) :
    (F.tangentDecomposition B N).hom ≫ biprod.fst = F.tangentAugmentation B N := sorry

/-- The `F(B)` summand enters the tangent decomposition through its canonical section. -/
theorem tangentDecomposition_inl_inv (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) :
    biprod.inl ≫ (F.tangentDecomposition B N).inv = F.tangentSection B N := sorry

/-- The tangent summand enters `F(B[N])` through the kernel inclusion. -/
theorem tangentDecomposition_inr_inv (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) :
    biprod.inr ≫ (F.tangentDecomposition B N).inv = F.tangentι B N := sorry

/-- The tangent object is the concrete kernel of the augmentation on `F(B[N])`. -/
theorem tangentObj_eq_kernel (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) :
    F.tangentObj B N = ModuleCat.of B.right (F.tangentAugmentation B N).hom.ker := sorry

/-- The semilinear tensor map induced by a morphism of algebra-module pairs. -/
noncomputable def tangentTensorMap (F : ModuleValuedFunctor.{u, u} A) {B B' : Under A}
    {N : ModuleCat.{u} B.right} {N' : ModuleCat.{u} B'.right}
    (f : ModulePair.Map B N B' N') :
    (N ⊗[B.right] F.obj B) →ₛₗ[f.base.right.hom] (N' ⊗[B'.right] F.obj B') :=
  TensorProduct.map f.linear (F.mapSemilinear f.base)

/-- Tensor transport along an identity pair morphism is the identity. -/
theorem tangentTensorMap_id (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) (x : N ⊗[B.right] F.obj B) :
    F.tangentTensorMap (ModulePair.Map.id B N) x = x := sorry

/-- Tensor transport respects composition of pair morphisms. -/
theorem tangentTensorMap_comp (F : ModuleValuedFunctor.{u, u} A) {B B' B'' : Under A}
    {N : ModuleCat.{u} B.right} {N' : ModuleCat.{u} B'.right}
    {N'' : ModuleCat.{u} B''.right} (f : ModulePair.Map B N B' N')
    (g : ModulePair.Map B' N' B'' N'') (x : N ⊗[B.right] F.obj B) :
    F.tangentTensorMap (ModulePair.Map.comp f g) x =
      F.tangentTensorMap g (F.tangentTensorMap f x) := sorry

/-- The pair functor `(B, N) ↦ N ⊗[B] F(B)`. -/
noncomputable def tangentTensor (F : ModuleValuedFunctor.{u, u} A) : ModulePairFunctor A where
  obj B N := N ⊗ F.obj B
  map f := F.tangentTensorMap f
  map_id B N := F.tangentTensorMap_id B N
  map_comp f g := F.tangentTensorMap_comp f g

/-- The tensor pair functor has value `N ⊗[B] F(B)` at `(B, N)`. -/
theorem tangentTensor_obj (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) : F.tangentTensor.obj B N = N ⊗ F.obj B := sorry

/-- The tensor pair functor acts on pure tensors by the two semilinear transition maps. -/
theorem tangentTensor_map_tmul (F : ModuleValuedFunctor.{u, u} A) {B B' : Under A}
    {N : ModuleCat.{u} B.right} {N' : ModuleCat.{u} B'.right}
    (f : ModulePair.Map B N B' N') (n : N) (x : F.obj B) :
    F.tangentTensor.map f (n ⊗ₜ[B.right] x) =
      f.linear n ⊗ₜ[B'.right] F.mapSemilinear f.base x := sorry

/-- The action of the square-zero ideal on the image of `F(B) ⟶ F(B[N])`. -/
noncomputable def squareZeroIdealAction (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) (n : N) (x : F.obj B) : F.squareZeroValue B N :=
  ((F.obj (ModulePair.squareZero B N)).smul
      (TrivSqZeroExt.inr n : (ModulePair.squareZero B N).right)).hom
    (F.map (ModulePair.inclusion B N) x)

/-- The square-zero ideal action is multiplication by `inr n` in `F(B[N])`. -/
theorem squareZeroIdealAction_apply (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) (n : N) (x : F.obj B) :
    F.squareZeroIdealAction B N n x =
      ((F.obj (ModulePair.squareZero B N)).smul
        (TrivSqZeroExt.inr n : (ModulePair.squareZero B N).right)).hom
          (F.map (ModulePair.inclusion B N) x) := sorry

/-- The square-zero multiplication formula is additive in its tangent argument. -/
theorem tensorToSquareZero_add_left (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) (n n' : N) (x : F.obj B) :
    F.squareZeroIdealAction B N (n + n') x =
      F.squareZeroIdealAction B N n x + F.squareZeroIdealAction B N n' x := sorry

/-- The square-zero multiplication formula is linear in its tangent argument. -/
theorem tensorToSquareZero_smul_left (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) (b : B.right) (n : N) (x : F.obj B) :
    F.squareZeroIdealAction B N (b • n) x =
      b • F.squareZeroIdealAction B N n x := sorry

/-- The square-zero multiplication formula is additive in the `F(B)` argument. -/
theorem tensorToSquareZero_add_right (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) (n : N) (x x' : F.obj B) :
    F.squareZeroIdealAction B N n (x + x') =
      F.squareZeroIdealAction B N n x + F.squareZeroIdealAction B N n x' := sorry

/-- The square-zero multiplication formula is linear in the `F(B)` argument. -/
theorem tensorToSquareZero_smul_right (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) (b : B.right) (n : N) (x : F.obj B) :
    F.squareZeroIdealAction B N n (b • x) =
      b • F.squareZeroIdealAction B N n x := sorry

/-- Multiplication by the square-zero ideal defines `N ⊗[B] F(B) ⟶ F(B[N])`. -/
noncomputable def tensorToSquareZero (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) : N ⊗ F.obj B ⟶ F.squareZeroValue B N :=
  ModuleCat.MonoidalCategory.tensorLift
    (F.squareZeroIdealAction B N)
    (F.tensorToSquareZero_add_left B N) (F.tensorToSquareZero_smul_left B N)
    (F.tensorToSquareZero_add_right B N) (F.tensorToSquareZero_smul_right B N)

/-- On a pure tensor, the square-zero multiplication map is multiplication by `inr n`. -/
theorem tensorToSquareZero_tmul (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) (n : N) (x : F.obj B) :
    F.tensorToSquareZero B N (n ⊗ₜ[B.right] x) =
      F.squareZeroIdealAction B N n x := sorry

/-- The square-zero multiplication map is killed by the tangent augmentation. -/
theorem tensorToSquareZero_comp_augmentation (F : ModuleValuedFunctor.{u, u} A)
    (B : Under A) (N : ModuleCat.{u} B.right) :
    F.tensorToSquareZero B N ≫ F.tangentAugmentation B N = 0 := sorry

/-- Every value of the square-zero multiplication map lies in the tangent kernel. -/
theorem tensorToSquareZero_mem (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) (x : N ⊗[B.right] F.obj B) :
    F.tensorToSquareZero B N x ∈ (F.tangentAugmentation B N).hom.ker := sorry

/-- The canonical component `N ⊗[B] F(B) ⟶ TF(B, N)` of the tangent comparison. -/
noncomputable def tensorToTangentApp (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) : F.tangentTensor.obj B N ⟶ F.tangentObj B N :=
  ModuleCat.ofHom <| LinearMap.codRestrict (F.tangentAugmentation B N).hom.ker
    (F.tensorToSquareZero B N).hom (F.tensorToSquareZero_mem B N)

/-- The tangent comparison components are natural in morphisms of algebra-module pairs. -/
theorem tensorToTangent_naturality (F : ModuleValuedFunctor.{u, u} A) {B B' : Under A}
    {N : ModuleCat.{u} B.right} {N' : ModuleCat.{u} B'.right}
    (f : ModulePair.Map B N B' N') (x : F.tangentTensor.obj B N) :
    F.tangent.map f (F.tensorToTangentApp B N x) =
      F.tensorToTangentApp B' N' (F.tangentTensor.map f x) := sorry

/-- The natural tensor comparison `N ⊗[B] F(B) ⟶ TF(B, N)` on algebra-module pairs. -/
noncomputable def tensorToTangent (F : ModuleValuedFunctor.{u, u} A) :
    ModulePairFunctor.Hom F.tangentTensor F.tangent where
  app B N := F.tensorToTangentApp B N
  naturality f := F.tensorToTangent_naturality f

/-- A tensor comparison component followed by the kernel inclusion is square-zero multiplication. -/
theorem tensorToTangent_app (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right) :
    F.tensorToTangent.app B N ≫ F.tangentι B N = F.tensorToSquareZero B N := sorry

/-- The tangent module at the zero module is a zero object. -/
theorem tangent_obj_zero (F : ModuleValuedFunctor.{u, u} A) (B : Under A) :
    IsZero (F.tangentObj B (0 : ModuleCat.{u} B.right)) := sorry

/-- A zero map of modules induces the zero map between their tangent modules. -/
theorem tangent_map_zero (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N N' : ModuleCat.{u} B.right) :
    (F.tangent.fixedBase B).map (0 : N ⟶ N') = 0 := sorry

end ModuleValuedFunctor
