/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.RankOneReflexive
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.InternalHom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products of rank-one reflexive modules

Reflexive tensor products induce a group law on isomorphism classes of rank-one reflexive coherent
modules on an integral locally Noetherian normal scheme.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]

variable {X}

/-- The morphism `(ihom ℱ).obj (𝟙_ X.Modules) ⊗ 𝒢 ⟶ (ihom ℱ).obj 𝒢` obtained by currying
evaluation. -/
noncomputable def dualTensorToInternalHom (ℱ 𝒢 : X.Modules) :
    (((ihom ℱ).obj (𝟙_ (X.Modules))) ⊗ 𝒢 : X.Modules) ⟶ (ihom ℱ).obj 𝒢 :=
  MonoidalClosed.curry (
    (α_ ℱ ((ihom ℱ).obj (𝟙_ (X.Modules))) 𝒢).inv ≫
    tensorHom ((ihom.ev ℱ).app (𝟙_ (X.Modules))) (𝟙 𝒢) ≫
    (λ_ 𝒢).hom)

/-- The comparison from the reflexive hull of `(ihom ℱ).obj (𝟙_ X.Modules) ⊗ 𝒢` to
`(ihom ℱ).obj 𝒢`. -/
@[stacks 0EBL]
noncomputable def reflexiveHullDualTensorToInternalHom
    (ℱ 𝒢 : X.Modules) [ℱ.IsCoherent] [𝒢.IsCoherent]
    [((((ihom ℱ).obj (𝟙_ (X.Modules))) ⊗ 𝒢 : X.Modules)).IsCoherent]
    [(((ihom ℱ).obj 𝒢)).IsCoherent] [IsReflexive ((ihom ℱ).obj 𝒢)] :
    reflexiveHull ((((ihom ℱ).obj (𝟙_ (X.Modules))) ⊗ 𝒢 : X.Modules)) ⟶
      (ihom ℱ).obj 𝒢 :=
  reflexiveHullMap (dualTensorToInternalHom ℱ 𝒢) ≫
    inv (toReflexiveHull ((ihom ℱ).obj 𝒢))

/-- For coherent reflexive modules on an integral locally Noetherian normal scheme, the comparison
from the reflexive hull of dual tensor to internal Hom is an isomorphism. -/
@[stacks 0EBL]
theorem isIso_reflexiveHullDualTensorToInternalHom
    (hXnormal : X.isNormal)
    (ℱ 𝒢 : X.Modules) [ℱ.IsCoherent] [𝒢.IsCoherent]
    [IsReflexive ℱ] [IsReflexive 𝒢] :
    IsIso (reflexiveHullDualTensorToInternalHom ℱ 𝒢) := sorry

/-- The tensor unit is a coherent reflexive module of rank one at the generic point. -/
theorem rankOneReflexiveModuleProperty_tensorUnit :
    rankOneReflexiveModuleProperty X (𝟙_ X.Modules) := sorry

/-- The reflexive hull of the tensor product of two rank-one coherent reflexive modules is again
rank-one coherent and reflexive. -/
theorem rankOneReflexiveModuleProperty_reflexiveHull_tensor
    (ℱ 𝒢 : RankOneReflexiveModule X) :
    rankOneReflexiveModuleProperty X (reflexiveHull (ℱ.obj ⊗ 𝒢.obj)) := sorry

/-- The dual of a rank-one coherent reflexive module is again rank-one coherent and reflexive. -/
theorem rankOneReflexiveModuleProperty_dual (ℱ : RankOneReflexiveModule X) :
    rankOneReflexiveModuleProperty X (dual ℱ.obj) := sorry

namespace RankOneReflexiveModule

/-- The structure module regarded as a rank-one coherent reflexive module. -/
noncomputable def unit : RankOneReflexiveModule X :=
  ⟨𝟙_ X.Modules, rankOneReflexiveModuleProperty_tensorUnit⟩

/-- The reflexive hull of the tensor product of two rank-one coherent reflexive modules. -/
noncomputable def tensor (ℱ 𝒢 : RankOneReflexiveModule X) : RankOneReflexiveModule X :=
  ⟨reflexiveHull (ℱ.obj ⊗ 𝒢.obj), rankOneReflexiveModuleProperty_reflexiveHull_tensor ℱ 𝒢⟩

/-- The dual of a rank-one coherent reflexive module. -/
noncomputable def dual (ℱ : RankOneReflexiveModule X) : RankOneReflexiveModule X :=
  ⟨AlgebraicGeometry.Scheme.Modules.dual ℱ.obj, rankOneReflexiveModuleProperty_dual ℱ⟩

end RankOneReflexiveModule

namespace RankOneReflexiveIsoClass

/-- Isomorphism classes of rank-one coherent reflexive modules form an additive commutative group:
addition is reflexive-hull tensor product, zero is the structure module, and negation is duality. -/
@[implicit_reducible, stacks 0EBL]
noncomputable def addCommGroup (hXnormal : X.isNormal) :
    AddCommGroup (RankOneReflexiveIsoClass X) := by
  let add : RankOneReflexiveIsoClass X → RankOneReflexiveIsoClass X →
      RankOneReflexiveIsoClass X :=
    fun x y ↦ toSkeleton (RankOneReflexiveModule.tensor x.out y.out)
  let zero : RankOneReflexiveIsoClass X :=
    toSkeleton (RankOneReflexiveModule.unit (X := X))
  let neg : RankOneReflexiveIsoClass X → RankOneReflexiveIsoClass X :=
    fun x ↦ toSkeleton (RankOneReflexiveModule.dual x.out)
  let nsmul : ℕ → RankOneReflexiveIsoClass X → RankOneReflexiveIsoClass X :=
    fun n x ↦ n.rec zero (fun _ y ↦ add y x)
  let zsmul : ℤ → RankOneReflexiveIsoClass X → RankOneReflexiveIsoClass X :=
    fun n x ↦ match n with
      | .ofNat k => nsmul k x
      | .negSucc k => neg (nsmul k.succ x)
  refine
    { add := add
      add_assoc := ?_
      zero := zero
      zero_add := ?_
      add_zero := ?_
      nsmul := nsmul
      nsmul_zero := ?_
      nsmul_succ := ?_
      neg := neg
      sub := fun x y ↦ add x (neg y)
      sub_eq_add_neg := ?_
      zsmul := zsmul
      zsmul_zero' := ?_
      zsmul_succ' := ?_
      zsmul_neg' := ?_
      neg_add_cancel := ?_
      add_comm := ?_ }
  all_goals sorry

/-- Addition in the rank-one reflexive class group is represented by reflexive-hull tensor
product. -/
@[stacks 0EBL]
theorem addCommGroup_add (hXnormal : X.isNormal) (ℱ 𝒢 : RankOneReflexiveModule X) :
    (addCommGroup hXnormal).add (toSkeleton ℱ) (toSkeleton 𝒢) =
      toSkeleton (RankOneReflexiveModule.tensor ℱ 𝒢) := sorry

end RankOneReflexiveIsoClass

/-- The additive commutative group of isomorphism classes of rank-one coherent reflexive
modules, bundled with its explicit reflexive-tensor group structure. -/
noncomputable def rankOneReflexiveClassGroup
    (hXnormal : X.isNormal) : AddCommGrpCat.{u + 1} where
  carrier := RankOneReflexiveIsoClass X
  str := RankOneReflexiveIsoClass.addCommGroup hXnormal

end AlgebraicGeometry.Scheme.Modules
