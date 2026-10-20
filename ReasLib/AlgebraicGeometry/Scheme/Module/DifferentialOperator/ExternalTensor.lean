/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.DifferentialOperator
public import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.FiniteOrder
public import ReasLib.AlgebraicGeometry.Scheme.Module.ExternalTensor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Differential operators on external tensor products

This file records one-sided and two-sided finite-order differential operators on external
tensor products, together with the bilinear external tensor product functor they determine.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.DifferentialOperator

/-- A differential operator on an external tensor product acts on every local pure tensor as
the given operator on the left factor and the identity on the right factor. -/
def IsExternalTensorProductRight
    {X S Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    {F F' : X.Modules} (G : Y.Modules) {k : ℕ}
    (D : Diff(a.toShHom ; k ; F, F'))
    (D' : Diff((Limits.pullback.snd a b).toShHom ; k ;
      externalTensorProduct a b F G, externalTensorProduct a b F' G)) : Prop :=
  ∀ (U : X.Opens) (V : Y.Opens) (s : Γ(F, U)) (t : Γ(G, V)),
    let W : (Limits.pullback a b).Opens :=
      Limits.pullback.fst a b ⁻¹ᵁ U ⊓ Limits.pullback.snd a b ⁻¹ᵁ V
    let sPullback :=
      ((((Scheme.Modules.pullback (Limits.pullback.fst a b)).obj F).val.map
        (homOfLE inf_le_left).op).hom)
        (((((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.fst a b)).unit.app F).val.app (op U)).hom) s)
    let tPullback :=
      ((((Scheme.Modules.pullback (Limits.pullback.snd a b)).obj G).val.map
        (homOfLE inf_le_right).op).hom)
        (((((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.snd a b)).unit.app G).val.app (op V)).hom) t)
    let Ds :=
      (((SheafOfModules.RingedSite.DifferentialOperators.toHom D).val.app (op U)).hom) s
    let DsPullback :=
      ((((Scheme.Modules.pullback (Limits.pullback.fst a b)).obj F').val.map
        (homOfLE inf_le_left).op).hom)
        (((((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.fst a b)).unit.app F').val.app (op U)).hom) Ds)
    ((SheafOfModules.RingedSite.DifferentialOperators.toHom D').val.app (op W)).hom
        (SheafOfModules.RingedSite.tensorSection
          (Limits.pullback a b).sheaf (op W) sPullback tPullback) =
      SheafOfModules.RingedSite.tensorSection (Limits.pullback a b).sheaf (op W)
        DsPullback tPullback

/-- An order-`k` differential operator extends uniquely to the external tensor product with a
quasicoherent right factor, relative to the second projection of the fiber product. -/
theorem existsUnique_externalTensorProductRight
    {X S Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (F F' : X.Modules) [F.IsQuasicoherent] [F'.IsQuasicoherent]
    (G : Y.Modules) [G.IsQuasicoherent] (k : ℕ)
    (D : Diff(a.toShHom ; k ; F, F')) :
    ∃! D' : Diff((Limits.pullback.snd a b).toShHom ; k ;
      externalTensorProduct a b F G, externalTensorProduct a b F' G),
      IsExternalTensorProductRight a b G D D' := sorry

/-- A finite-order operator on an external tensor product acts on every local pure tensor by
applying the two given operators to its factors. -/
def IsExternalTensorProduct
    {X S Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    {F F' : X.Modules} {G G' : Y.Modules}
    (D : SheafOfModules.RingedSite.DifferentialOperators.FiniteOrder
      (J := Opens.grothendieckTopology X)
      (RingedSpace.Hom.inverseImageStructureSheafHomComm a.toShHom) F F')
    (E : SheafOfModules.RingedSite.DifferentialOperators.FiniteOrder
      (J := Opens.grothendieckTopology Y)
      (RingedSpace.Hom.inverseImageStructureSheafHomComm b.toShHom) G G')
    (DE : SheafOfModules.RingedSite.DifferentialOperators.FiniteOrder
      (J := Opens.grothendieckTopology (Limits.pullback a b : Scheme.{u}))
      (RingedSpace.Hom.inverseImageStructureSheafHomComm
        (Limits.pullback.fst a b ≫ a).toShHom)
      (externalTensorProduct a b F G) (externalTensorProduct a b F' G')) : Prop :=
  ∀ (U : X.Opens) (V : Y.Opens) (s : Γ(F, U)) (t : Γ(G, V)),
    let W : (Limits.pullback a b).Opens :=
      Limits.pullback.fst a b ⁻¹ᵁ U ⊓ Limits.pullback.snd a b ⁻¹ᵁ V
    let sPullback :=
      ((((Scheme.Modules.pullback (Limits.pullback.fst a b)).obj F).val.map
        (homOfLE inf_le_left).op).hom)
        (((((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.fst a b)).unit.app F).val.app (op U)).hom) s)
    let tPullback :=
      ((((Scheme.Modules.pullback (Limits.pullback.snd a b)).obj G).val.map
        (homOfLE inf_le_right).op).hom)
        (((((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.snd a b)).unit.app G).val.app (op V)).hom) t)
    let Ds :=
      (((SheafOfModules.RingedSite.DifferentialOperators.FiniteOrder.toHom D).val.app
        (op U)).hom) s
    let Et :=
      (((SheafOfModules.RingedSite.DifferentialOperators.FiniteOrder.toHom E).val.app
        (op V)).hom) t
    let DsPullback :=
      ((((Scheme.Modules.pullback (Limits.pullback.fst a b)).obj F').val.map
        (homOfLE inf_le_left).op).hom)
        (((((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.fst a b)).unit.app F').val.app (op U)).hom) Ds)
    let EtPullback :=
      ((((Scheme.Modules.pullback (Limits.pullback.snd a b)).obj G').val.map
        (homOfLE inf_le_right).op).hom)
        (((((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.snd a b)).unit.app G').val.app (op V)).hom) Et)
    ((SheafOfModules.RingedSite.DifferentialOperators.FiniteOrder.toHom DE).val.app
        (op W)).hom
        (SheafOfModules.RingedSite.tensorSection
          (Limits.pullback a b).sheaf (op W) sPullback tPullback) =
      SheafOfModules.RingedSite.tensorSection (Limits.pullback a b).sheaf (op W)
        DsPullback EtPullback

/-- Two finite-order relative differential operators determine a unique finite-order operator
on their external tensor products, characterized on local pure tensors. -/
theorem existsUnique_externalTensorProduct
    {X S Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    {F F' : X.Modules} [F.IsQuasicoherent] [F'.IsQuasicoherent]
    {G G' : Y.Modules} [G.IsQuasicoherent] [G'.IsQuasicoherent]
    (D : SheafOfModules.RingedSite.DifferentialOperators.FiniteOrder
      (J := Opens.grothendieckTopology X)
      (RingedSpace.Hom.inverseImageStructureSheafHomComm a.toShHom) F F')
    (E : SheafOfModules.RingedSite.DifferentialOperators.FiniteOrder
      (J := Opens.grothendieckTopology Y)
      (RingedSpace.Hom.inverseImageStructureSheafHomComm b.toShHom) G G') :
    ∃! DE : SheafOfModules.RingedSite.DifferentialOperators.FiniteOrder
      (J := Opens.grothendieckTopology (Limits.pullback a b : Scheme.{u}))
      (RingedSpace.Hom.inverseImageStructureSheafHomComm
        (Limits.pullback.fst a b ≫ a).toShHom)
      (externalTensorProduct a b F G) (externalTensorProduct a b F' G'),
      IsExternalTensorProduct a b D E DE := sorry

end AlgebraicGeometry.Scheme.Modules.DifferentialOperator

namespace AlgebraicGeometry.Scheme.Hom

/-- A functor between finite-order differential-operator categories is the external tensor
product functor when it has the usual object formula, acts on local pure tensors by the two
input operators, preserves identities and composition, and is additive in each variable. -/
structure IsExternalTensorProductFunctor
    {X S Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (T : FiniteOrderDifferentialOperatorCat a × FiniteOrderDifferentialOperatorCat b ⥤
      FiniteOrderDifferentialOperatorCat (Limits.pullback.fst a b ≫ a)) : Prop where
  /-- The object map is the external tensor product of the underlying quasicoherent modules. -/
  obj_eq (F : FiniteOrderDifferentialOperatorCat a)
      (G : FiniteOrderDifferentialOperatorCat b) :
    FiniteOrderDifferentialOperatorCat.underlying (Limits.pullback.fst a b ≫ a)
        (T.obj (F, G)) =
      Scheme.Modules.externalTensorProduct a b
        (FiniteOrderDifferentialOperatorCat.underlying a F)
        (FiniteOrderDifferentialOperatorCat.underlying b G)
  /-- On morphisms, the functor applies the two operators to the corresponding factors of
  every local pure tensor. -/
  map_isExternalTensorProduct
      {F F' : FiniteOrderDifferentialOperatorCat a}
      {G G' : FiniteOrderDifferentialOperatorCat b}
      (D : F ⟶ F') (E : G ⟶ G') :
    Scheme.Modules.DifferentialOperator.IsExternalTensorProduct a b D E
      (FiniteOrderDifferentialOperatorCat.transport (Limits.pullback.fst a b ≫ a)
        (obj_eq F G) (obj_eq F' G')
        (T.map ((D, E) : (F, G) ⟶ (F', G'))))
  /-- The specified morphism action preserves pairs of identity operators. -/
  map_id (F : FiniteOrderDifferentialOperatorCat a)
      (G : FiniteOrderDifferentialOperatorCat b) :
    T.map (𝟙 F, 𝟙 G) = 𝟙 (T.obj (F, G))
  /-- The specified morphism action preserves simultaneous composition. -/
  map_comp
      {F₁ F₂ F₃ : FiniteOrderDifferentialOperatorCat a}
      {G₁ G₂ G₃ : FiniteOrderDifferentialOperatorCat b}
      (D₁ : F₁ ⟶ F₂) (D₂ : F₂ ⟶ F₃)
      (E₁ : G₁ ⟶ G₂) (E₂ : G₂ ⟶ G₃) :
    T.map ((D₁ ≫ D₂, E₁ ≫ E₂) : (F₁, G₁) ⟶ (F₃, G₃)) =
      T.map ((D₁, E₁) : (F₁, G₁) ⟶ (F₂, G₂)) ≫
        T.map ((D₂, E₂) : (F₂, G₂) ⟶ (F₃, G₃))
  /-- The specified morphism action is additive in its first variable. -/
  map_add_left
      {F F' : FiniteOrderDifferentialOperatorCat a}
      {G G' : FiniteOrderDifferentialOperatorCat b}
      (D D' : F ⟶ F') (E : G ⟶ G') :
    T.map ((D + D', E) : (F, G) ⟶ (F', G')) =
      T.map ((D, E) : (F, G) ⟶ (F', G')) +
        T.map ((D', E) : (F, G) ⟶ (F', G'))
  /-- The specified morphism action is additive in its second variable. -/
  map_add_right
      {F F' : FiniteOrderDifferentialOperatorCat a}
      {G G' : FiniteOrderDifferentialOperatorCat b}
      (D : F ⟶ F') (E E' : G ⟶ G') :
    T.map ((D, E + E') : (F, G) ⟶ (F', G')) =
      T.map ((D, E) : (F, G) ⟶ (F', G')) +
        T.map ((D, E') : (F, G) ⟶ (F', G'))

namespace IsExternalTensorProductFunctor

/-- The object comparison supplied by an external tensor product functor specification. -/
noncomputable def objIso
    {X S Y : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S}
    {T : FiniteOrderDifferentialOperatorCat a × FiniteOrderDifferentialOperatorCat b ⥤
      FiniteOrderDifferentialOperatorCat (Limits.pullback.fst a b ≫ a)}
    (h : IsExternalTensorProductFunctor a b T)
    (F : FiniteOrderDifferentialOperatorCat a)
    (G : FiniteOrderDifferentialOperatorCat b) :
    FiniteOrderDifferentialOperatorCat.underlying (Limits.pullback.fst a b ≫ a)
        (T.obj (F, G)) ≅
      Scheme.Modules.externalTensorProduct a b
        (FiniteOrderDifferentialOperatorCat.underlying a F)
        (FiniteOrderDifferentialOperatorCat.underlying b G) :=
  eqToIso (h.obj_eq F G)

end IsExternalTensorProductFunctor

/-- There is a unique functor on quasicoherent modules and finite-order relative differential
operators whose object map is external tensor product and whose morphism map applies the two
operators separately to local pure tensors; it is additive in each variable. -/
theorem existsUnique_externalTensorProductFunctor
    {X S Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) :
    ∃! T : FiniteOrderDifferentialOperatorCat a × FiniteOrderDifferentialOperatorCat b ⥤
      FiniteOrderDifferentialOperatorCat (Limits.pullback.fst a b ≫ a),
      IsExternalTensorProductFunctor a b T := sorry

end AlgebraicGeometry.Scheme.Hom
