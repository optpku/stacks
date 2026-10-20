/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Indiscrete
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.Topology.Sheaves.Ring.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal module sheaves on indiscrete spaces

For a commutative ring sheaf on a nonempty indiscrete space, generation from the top open is
strong monoidal.  The tensorator is built explicitly from the bilinear universal properties of
module tensor products and module-sheaf tensor products; only naturality and coherence laws are
deferred.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u

namespace TopCat.Sheaf.ringSheafOfComm

/-- The section rings of the underlying ring sheaf retain their canonical commutative ring
structure. -/
@[stacks 01BH "commutative sections of an underlying ring sheaf"]
instance commRing {X : TopCat.{u}} (O : TopCat.Sheaf CommRingCat.{u} X)
    (U : (Opens X)ᵒᵖ) : CommRing ((TopCat.Sheaf.ringSheafOfComm O).obj.obj U) :=
  inferInstanceAs (CommRing (O.obj.obj U))

end TopCat.Sheaf.ringSheafOfComm

namespace SheafOfModules.Indiscrete

variable {X : TopCat.{u}} [IndiscreteTopology X] [Nonempty X]
variable (O : TopCat.Sheaf CommRingCat.{u} X)

variable {G H K : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm O)}

/-- The components of a restriction-compatible bilinear map on an indiscrete space,
reconstructed from its component on the top open. -/
public noncomputable def bilinearMapOfTopApp
    (b : G.val.obj (op (⊤ : Opens X)) →ₗ[O.obj.obj (op ⊤)]
      H.val.obj (op ⊤) →ₗ[O.obj.obj (op ⊤)] K.val.obj (op ⊤))
    (U : (Opens X)ᵒᵖ) :
    G.val.obj U →ₗ[O.obj.obj U] H.val.obj U →ₗ[O.obj.obj U] K.val.obj U :=
  @dite
    (G.val.obj U →ₗ[O.obj.obj U] H.val.obj U →ₗ[O.obj.obj U] K.val.obj U)
    (U = op (⊤ : Opens X)) (Classical.propDecidable _)
    (fun hU ↦
      Eq.mp
        (congrArg
          (fun V : (Opens X)ᵒᵖ ↦
            G.val.obj V →ₗ[O.obj.obj V] H.val.obj V →ₗ[O.obj.obj V] K.val.obj V)
          hU).symm
        b)
    (fun _ ↦ 0)

/-- The bilinear components reconstructed from the top open commute with restrictions. -/
theorem bilinearMapOfTopApp_naturality
    (b : G.val.obj (op (⊤ : Opens X)) →ₗ[O.obj.obj (op ⊤)]
      H.val.obj (op ⊤) →ₗ[O.obj.obj (op ⊤)] K.val.obj (op ⊤))
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (x : G.val.obj U) (y : H.val.obj U) :
    K.val.map i (bilinearMapOfTopApp O b U x y) =
      bilinearMapOfTopApp O b V (G.val.map i x) (H.val.map i y) := sorry

/-- A restriction-compatible bilinear map on an indiscrete space, reconstructed from its
component on the top open. -/
@[stacks 01BH "bilinear maps reconstructed from the top open"]
public noncomputable def bilinearMapOfTop
    (b : G.val.obj (op (⊤ : Opens X)) →ₗ[O.obj.obj (op ⊤)]
      H.val.obj (op ⊤) →ₗ[O.obj.obj (op ⊤)] K.val.obj (op ⊤)) :
    SheafOfModules.RingedSite.SectionBilinearMap
      (J := Opens.grothendieckTopology X) O G H K where
  app := bilinearMapOfTopApp O b
  naturality := bilinearMapOfTopApp_naturality O b

/-- Reconstructing an indiscrete bilinear map recovers its prescribed top-open component. -/
@[simp]
theorem bilinearMapOfTop_app_top
    (b : G.val.obj (op (⊤ : Opens X)) →ₗ[O.obj.obj (op ⊤)]
      H.val.obj (op ⊤) →ₗ[O.obj.obj (op ⊤)] K.val.obj (op ⊤)) :
    (bilinearMapOfTop O b).app (op (⊤ : Opens X)) = b := sorry

/-- The top-open bilinear map from two generated module sheaves to the generated sheaf of their
module tensor product. -/
noncomputable def tensorBilinearTop
    (M N : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X)))) :
    ((ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj M).val.obj (op ⊤) →ₗ[O.obj.obj (op ⊤)]
      ((ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj N).val.obj (op ⊤) →ₗ[O.obj.obj (op ⊤)]
        ((ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj (M ⊗ N)).val.obj
          (op ⊤) :=
  ((TensorProduct.mk _ M N).compl₁₂
      (topValueIso (R := TopCat.Sheaf.ringSheafOfComm O) M).hom.hom
      (topValueIso (R := TopCat.Sheaf.ringSheafOfComm O) N).hom.hom).compr₂
    (topValueIso (R := TopCat.Sheaf.ringSheafOfComm O) (M ⊗ N)).inv.hom

/-- The canonical restriction-compatible bilinear map defining the tensorator of generation from
the top open. -/
noncomputable def tensorBilinear
    (M N : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X)))) :
    SheafOfModules.RingedSite.SectionBilinearMap
      (J := Opens.grothendieckTopology X) O
      ((ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj M)
      ((ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj N)
      ((ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj (M ⊗ N)) :=
  bilinearMapOfTop O (tensorBilinearTop O M N)

/-- The forward tensorator for generation of module sheaves from the top open. -/
noncomputable def tensorHom
    (M N : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X)))) :
    (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj M ⊗
        (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj N ⟶
      (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj (M ⊗ N) :=
  (tensorBilinear O M N).hom

/-- The pure-tensor function on top-open modules, valued in the top sections of the tensor product
of their generated sheaves. -/
noncomputable def tensorLiftPureTop
    (M N : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X))))
    (x : M) (y : N) :
    (((ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj M ⊗
      (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj N).val.obj (op ⊤)) :=
  SheafOfModules.RingedSite.tensorSection O (op ⊤)
    ((topValueIso (R := TopCat.Sheaf.ringSheafOfComm O) M).inv x)
    ((topValueIso (R := TopCat.Sheaf.ringSheafOfComm O) N).inv y)

/-- The top-open pure-tensor map is additive in its right argument. -/
theorem tensorLiftPureTop_add_right
    (M N : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X))))
    (x : M) (y y' : N) :
    tensorLiftPureTop O M N x (y + y') =
      tensorLiftPureTop O M N x y + tensorLiftPureTop O M N x y' := sorry

/-- The top-open pure-tensor map is linear in its right argument. -/
theorem tensorLiftPureTop_smul_right
    (M N : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X))))
    (x : M) (r : (TopCat.Sheaf.ringSheafOfComm O).obj.obj (op ⊤)) (y : N) :
    tensorLiftPureTop O M N x (r • y) = r • tensorLiftPureTop O M N x y := sorry

/-- Right-linear top-open pure tensoring for the inverse tensorator. -/
noncomputable def tensorLiftRightTop
    (M N : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X))))
    (x : M) :
    N →ₗ[(TopCat.Sheaf.ringSheafOfComm O).obj.obj (op ⊤)]
      (((ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj M ⊗
        (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj N).val.obj (op ⊤)) where
  toFun := tensorLiftPureTop O M N x
  map_add' := tensorLiftPureTop_add_right O M N x
  map_smul' := tensorLiftPureTop_smul_right O M N x

/-- Right-linear top-open pure tensoring is additive in its left argument. -/
theorem tensorLiftRightTop_add
    (M N : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X))))
    (x x' : M) :
    tensorLiftRightTop O M N (x + x') =
      tensorLiftRightTop O M N x + tensorLiftRightTop O M N x' := sorry

/-- Right-linear top-open pure tensoring is linear in its left argument. -/
theorem tensorLiftRightTop_smul
    (M N : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X))))
    (r : (TopCat.Sheaf.ringSheafOfComm O).obj.obj (op ⊤)) (x : M) :
    tensorLiftRightTop O M N (r • x) = r • tensorLiftRightTop O M N x := sorry

/-- The bilinear top-open pure-tensor map defining the inverse tensorator. -/
@[stacks 01BH "bilinear top-open map for the inverse tensorator"]
noncomputable def tensorLiftBilinearTop
    (M N : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X)))) :
    M →ₗ[(TopCat.Sheaf.ringSheafOfComm O).obj.obj (op ⊤)]
      N →ₗ[(TopCat.Sheaf.ringSheafOfComm O).obj.obj (op ⊤)]
        (((ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj M ⊗
          (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj N).val.obj (op ⊤)) where
  toFun := tensorLiftRightTop O M N
  map_add' := tensorLiftRightTop_add O M N
  map_smul' := tensorLiftRightTop_smul O M N

/-- The tensor lift from the tensor product of two top-open modules to the top value of the
tensor product of their generated sheaves. -/
noncomputable def tensorLiftTop
    (M N : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X)))) :
    M ⊗ N ⟶
      (((ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj M ⊗
        (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj N).val.obj (op ⊤)) :=
  ModuleCat.ofHom (TensorProduct.lift (tensorLiftBilinearTop O M N))

/-- The inverse tensorator for generation of module sheaves from the top open. -/
noncomputable def tensorInv
    (M N : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X)))) :
    (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj (M ⊗ N) ⟶
      (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj M ⊗
        (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj N :=
  homOfTop _ _
    ((topValueIso (R := TopCat.Sheaf.ringSheafOfComm O) (M ⊗ N)).hom ≫
      tensorLiftTop O M N)

/-- The forward and inverse tensorators compose to the identity on the tensor product sheaf. -/
theorem tensorHom_tensorInv
    (M N : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X)))) :
    tensorHom O M N ≫ tensorInv O M N =
      𝟙 ((ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj M ⊗
        (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj N) := sorry

/-- The inverse and forward tensorators compose to the identity on the generated tensor sheaf. -/
theorem tensorInv_tensorHom
    (M N : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X)))) :
    tensorInv O M N ≫ tensorHom O M N =
      𝟙 ((ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj (M ⊗ N)) := sorry

/-- Generation from the top open canonically preserves tensor products. -/
@[stacks 01BH "tensor products on an indiscrete space"]
noncomputable def tensorIso
    (M N : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X)))) :
    (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj M ⊗
        (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj N ≅
      (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj (M ⊗ N) where
  hom := tensorHom O M N
  inv := tensorInv O M N
  hom_inv_id := tensorHom_tensorInv O M N
  inv_hom_id := tensorInv_tensorHom O M N

/-- Generation from the top open canonically preserves the tensor unit. -/
@[stacks 01BH "tensor unit on an indiscrete space"]
noncomputable def unitTensorIso :
    𝟙_ (SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm O)) ≅
      (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj
        (𝟙_ (ModuleCat.{u}
          ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X))))) :=
  (SheafOfModules.RingedSite.unitIsoTensorUnit
      (J := Opens.grothendieckTopology X) (𝒪 := O)).symm ≪≫
    isoOfTop _ _
      (topValueIso (R := TopCat.Sheaf.ringSheafOfComm O)
        (𝟙_ (ModuleCat.{u}
          ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X)))))).symm

/-- Naturality of the inverse tensorator in its left argument. -/
theorem tensorIso_inv_natural_left
    {M M' : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X)))}
    (f : M ⟶ M')
    (N : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X)))) :
    (tensorIso O M N).inv ≫
        (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).map f ▷
          (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj N =
      (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).map (f ▷ N) ≫
        (tensorIso O M' N).inv := sorry

/-- Naturality of the inverse tensorator in its right argument. -/
theorem tensorIso_inv_natural_right
    {N N' : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X)))}
    (M : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X))))
    (f : N ⟶ N') :
    (tensorIso O M N).inv ≫
        (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj M ◁
          (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).map f =
      (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).map (M ◁ f) ≫
        (tensorIso O M N').inv := sorry

/-- Associativity coherence of the inverse tensorator. -/
theorem tensorIso_inv_associativity
    (M N P : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X)))) :
    (tensorIso O (M ⊗ N) P).inv ≫
        (tensorIso O M N).inv ▷
          (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj P ≫
        (α_ ((ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj M)
          ((ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj N)
          ((ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj P)).hom =
      (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).map (α_ M N P).hom ≫
        (tensorIso O M (N ⊗ P)).inv ≫
          (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj M ◁
            (tensorIso O N P).inv := sorry

/-- Left-unit coherence of the inverse tensorator. -/
theorem tensorIso_inv_left_unitality
    (M : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X)))) :
    (λ_ ((ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj M)).inv =
      (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).map (λ_ M).inv ≫
        (tensorIso O (𝟙_ _) M).inv ≫
          (unitTensorIso O).inv ▷
            (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj M := sorry

/-- Right-unit coherence of the inverse tensorator. -/
theorem tensorIso_inv_right_unitality
    (M : ModuleCat.{u}
      ((TopCat.Sheaf.ringSheafOfComm O).obj.obj (op (⊤ : Opens X)))) :
    (ρ_ ((ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj M)).inv =
      (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).map (ρ_ M).inv ≫
        (tensorIso O M (𝟙_ _)).inv ≫
          (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).obj M ◁
            (unitTensorIso O).inv := sorry

/-- The concrete strong-monoidal core for generation of module sheaves from the top open. -/
@[stacks 01BH "strong monoidal core of top-open generation"]
noncomputable def ofTopFunctorCoreMonoidal :
    (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).CoreMonoidal :=
  Functor.CoreMonoidal.mk' (unitTensorIso O) (tensorIso O)
    (tensorIso_inv_natural_left O) (tensorIso_inv_natural_right O)
    (tensorIso_inv_associativity O) (tensorIso_inv_left_unitality O)
    (tensorIso_inv_right_unitality O)

/-- Generation of module sheaves from the top open of a nonempty indiscrete space is canonically
strong monoidal. -/
@[stacks 01BH "monoidal generation from the top open", implicit_reducible]
noncomputable instance ofTopFunctorMonoidal :
    (ofTopFunctor (TopCat.Sheaf.ringSheafOfComm O)).Monoidal :=
  (ofTopFunctorCoreMonoidal O).toMonoidal

end SheafOfModules.Indiscrete
