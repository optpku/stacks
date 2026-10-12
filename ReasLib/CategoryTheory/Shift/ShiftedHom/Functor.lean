/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Functor.Currying
public import ReasLib.Algebra.Module.ULift
public import ReasLib.CategoryTheory.Shift.ShiftedHom.ModuleCat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transport of Shifted Morphisms by Functors

This leaf packages the canonical action of a shift-compatible functor on shifted morphisms.
The functorial linear map is the basic owner; an equivalence and chosen endpoint
identifications then give a linear equivalence between arbitrary shifted Hom modules.
-/

@[expose] public section

noncomputable section

universe uR vC uC vD uD vE uE vS

namespace CategoryTheory

variable {R : Type uR} [Ring R]
variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [HasShift C ℤ] [HasShift D ℤ]

/-- Transport a shifted morphism by a shift-compatible functor and chosen identifications of
both endpoint images. -/
@[stacks 0G1X "shifted Hom transport by a compatible functor"]
def Functor.shiftedHomMap (F : CategoryTheory.Functor C D) [F.CommShift ℤ]
    {X X' : C} {Y Y' : D} (hX : F.obj X ≅ Y) (hY : F.obj X' ≅ Y')
    (n : ℤ) : ShiftedHom X X' n → ShiftedHom Y Y' n :=
  fun f ↦ hX.inv ≫ ShiftedHom.map f F ≫ (shiftFunctor D n).map hY.hom

/-- Shifted-Hom transport by a functor is its shifted image conjugated by the endpoint
identifications. -/
@[simp]
theorem Functor.shiftedHomMap_apply (F : CategoryTheory.Functor C D) [F.CommShift ℤ]
    {X X' : C} {Y Y' : D} (hX : F.obj X ≅ Y) (hY : F.obj X' ≅ Y')
    (n : ℤ) (f : ShiftedHom X X' n) :
    F.shiftedHomMap hX hY n f =
      hX.inv ≫ ShiftedHom.map f F ≫ (shiftFunctor D n).map hY.hom := sorry

/-- The action of an additive, linear, shift-compatible functor on shifted Hom modules. -/
@[stacks 0G1X "linear shifted Hom transport by a compatible functor"]
noncomputable def Functor.shiftedHomLinearMap
    [Preadditive C] [Preadditive D]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    (F : CategoryTheory.Functor C D) [F.CommShift ℤ] [F.Additive] [F.Linear R]
    (X Y : C) (n : ℤ) :
    ShiftedHom X Y n →ₗ[R] ShiftedHom (F.obj X) (F.obj Y) n where
  toFun := fun f ↦ ShiftedHom.map f F
  map_add' := sorry
  map_smul' := sorry

/-- The underlying function of `shiftedHomLinearMap` is the canonical `ShiftedHom.map`. -/
@[simp]
theorem Functor.shiftedHomLinearMap_apply
    [Preadditive C] [Preadditive D]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    (F : CategoryTheory.Functor C D) [F.CommShift ℤ] [F.Additive] [F.Linear R]
    (X Y : C) (n : ℤ) (f : ShiftedHom X Y n) :
    Functor.shiftedHomLinearMap (R := R) F X Y n f =
      ShiftedHom.map f F := sorry

/-- The shifted-Hom bifunctor, with its two endpoints ordered as source and target. -/
@[stacks 0G1X "linear shifted Hom bifunctor"]
def ShiftedHom.bifunctor
    (R : Type uR) [Ring R] (C : Type uC) [Category.{vC} C]
    [Preadditive C] [CategoryTheory.Linear R C] [HasShift C ℤ] (n : ℤ) :
    Cᵒᵖ × C ⥤ ModuleCat.{vC} R :=
  Functor.uncurry.obj (ShiftedHom.linearCoyoneda R C n)

/-- A universe-lifted shifted-Hom bifunctor.  The lift is explicit so that a functor between
categories with different Hom universes still has a single module-valued codomain. -/
@[stacks 0G1X "universe-lifted linear shifted Hom bifunctor"]
def ShiftedHom.uliftBifunctor
    (R : Type uR) [Ring R] (C : Type uC) [Category.{vC} C]
    [Preadditive C] [CategoryTheory.Linear R C] [HasShift C ℤ]
    (n : ℤ) : Cᵒᵖ × C ⥤ ModuleCat.{max vC uE} R :=
  ShiftedHom.bifunctor R C n ⋙ ModuleCat.uliftFunctor.{uE} R

/-- Naturality in both endpoints of the lifted linear action of a shift-compatible functor. -/
@[reassoc, stacks 0G1X "naturality of the lifted shifted Hom action"]
theorem Functor.uliftShiftedHomNatTrans_naturality
    [Preadditive C] [Preadditive D]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    (F : CategoryTheory.Functor C D) [F.CommShift ℤ] [F.Additive] [F.Linear R]
    (n : ℤ) {X Y : Cᵒᵖ × C} (f : X ⟶ Y) :
    (ShiftedHom.uliftBifunctor.{uR, vC, uC, max vC vD} R C n).map f ≫
        ModuleCat.ofHom
          (LinearMap.ulift
            (F.shiftedHomLinearMap (R := R) Y.1.unop Y.2 n)) =
      ModuleCat.ofHom
          (LinearMap.ulift
            (F.shiftedHomLinearMap (R := R) X.1.unop X.2 n)) ≫
        ((F.op.prod F) ⋙
          ShiftedHom.uliftBifunctor.{uR, vD, uD, max vC vD} R D n).map f := sorry

/-- An additive, linear, shift-compatible functor acts naturally on the universe-lifted
shifted-Hom bifunctors. -/
@[stacks 0G1X "functorial action on the linear shifted Hom bifunctor"]
noncomputable def Functor.uliftShiftedHomNatTrans
    [Preadditive C] [Preadditive D]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    (F : CategoryTheory.Functor C D) [F.CommShift ℤ] [F.Additive] [F.Linear R]
    (n : ℤ) :
    ShiftedHom.uliftBifunctor.{uR, vC, uC, max vC vD} R C n ⟶
      (F.op.prod F) ⋙
        ShiftedHom.uliftBifunctor.{uR, vD, uD, max vC vD} R D n where
  app X := ModuleCat.ofHom
    (LinearMap.ulift
      (F.shiftedHomLinearMap (R := R) X.1.unop X.2 n))
  naturality _ _ f := F.uliftShiftedHomNatTrans_naturality n f

/-- The component of `uliftShiftedHomNatTrans` is the lifted canonical linear action. -/
@[simp]
theorem Functor.uliftShiftedHomNatTrans_app
    [Preadditive C] [Preadditive D]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    (F : CategoryTheory.Functor C D) [F.Additive] [F.CommShift ℤ] [F.Linear R]
    (n : ℤ) (X : Cᵒᵖ × C) :
    (F.uliftShiftedHomNatTrans (R := R) n).app X =
      ModuleCat.ofHom
        (LinearMap.ulift
          (F.shiftedHomLinearMap (R := R) X.1.unop X.2 n)) := sorry

/-- Naturality in both endpoints of the linear action of a shift-compatible functor when the
source and target categories have the same Hom universe. -/
@[reassoc, stacks 0G1X "naturality of the same-universe shifted Hom action"]
theorem Functor.shiftedHomNatTrans_naturality
    {C : Type uC} {D : Type uD}
    [Category.{vS} C] [Category.{vS} D]
    [Preadditive C] [Preadditive D]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] [F.Additive] [F.Linear R]
    (n : ℤ) {X Y : Cᵒᵖ × C} (f : X ⟶ Y) :
    (ShiftedHom.bifunctor R C n).map f ≫
        ModuleCat.ofHom (F.shiftedHomLinearMap (R := R) Y.1.unop Y.2 n) =
      ModuleCat.ofHom (F.shiftedHomLinearMap (R := R) X.1.unop X.2 n) ≫
        ((F.op.prod F) ⋙ ShiftedHom.bifunctor R D n).map f := sorry

/-- A functor between categories with the same Hom universe acts naturally on shifted-Hom
bifunctors without inserting an additional `ULift`. -/
@[stacks 0G1X "same-universe functorial action on shifted Hom"]
noncomputable def Functor.shiftedHomNatTrans
    {C : Type uC} {D : Type uD}
    [Category.{vS} C] [Category.{vS} D]
    [Preadditive C] [Preadditive D]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] [F.Additive] [F.Linear R] (n : ℤ) :
    ShiftedHom.bifunctor R C n ⟶
      (F.op.prod F) ⋙ ShiftedHom.bifunctor R D n where
  app X := ModuleCat.ofHom
    (F.shiftedHomLinearMap (R := R) X.1.unop X.2 n)
  naturality _ _ f := F.shiftedHomNatTrans_naturality n f

/-- The component of the same-universe shifted-Hom action is the canonical linear map induced by
the functor. -/
@[simp]
theorem Functor.shiftedHomNatTrans_app
    {C : Type uC} {D : Type uD}
    [Category.{vS} C] [Category.{vS} D]
    [Preadditive C] [Preadditive D]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] [F.Additive] [F.Linear R] (n : ℤ)
    (X : Cᵒᵖ × C) :
    (F.shiftedHomNatTrans (R := R) n).app X =
      ModuleCat.ofHom
        (F.shiftedHomLinearMap (R := R) X.1.unop X.2 n) := sorry

/-- The endpoint-identified action of an additive, linear, shift-compatible functor on shifted Hom
modules. -/
@[stacks 0G1X "endpoint-identified linear shifted Hom transport"]
noncomputable def Functor.shiftedHomLinearMapOfIsos
    [Preadditive C] [Preadditive D]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    (F : CategoryTheory.Functor C D) [F.CommShift ℤ] [F.Additive] [F.Linear R]
    {X X' : C} {Y Y' : D} (hX : F.obj X ≅ Y) (hY : F.obj X' ≅ Y')
    (n : ℤ) : ShiftedHom X X' n →ₗ[R] ShiftedHom Y Y' n where
  toFun := F.shiftedHomMap hX hY n
  map_add' := sorry
  map_smul' := sorry

/-- The endpoint-identified linear map has `Functor.shiftedHomMap` as its underlying
function. -/
@[simp]
theorem Functor.shiftedHomLinearMapOfIsos_apply
    [Preadditive C] [Preadditive D]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    (F : CategoryTheory.Functor C D) [F.CommShift ℤ] [F.Additive] [F.Linear R]
    {X X' : C} {Y Y' : D} (hX : F.obj X ≅ Y) (hY : F.obj X' ≅ Y')
    (n : ℤ) (f : ShiftedHom X X' n) :
    F.shiftedHomLinearMapOfIsos (R := R) hX hY n f =
      F.shiftedHomMap hX hY n f := sorry

namespace Equivalence

variable {R : Type uR} [Ring R]
variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [HasShift C ℤ] [HasShift D ℤ]

/-- Transport a shifted morphism along an equivalence and chosen identifications of both
endpoints. -/
@[stacks 09S9 "shifted Hom transport along an equivalence"]
def shiftedHomMap (e : C ≌ D) [e.functor.CommShift ℤ]
    {X X' : C} {Y Y' : D} (hX : e.functor.obj X ≅ Y)
    (hY : e.functor.obj X' ≅ Y') (n : ℤ) :
    ShiftedHom X X' n → ShiftedHom Y Y' n :=
  e.functor.shiftedHomMap hX hY n

/-- Shifted-Hom transport is the shifted image conjugated by the chosen endpoint
identifications. -/
@[simp]
theorem shiftedHomMap_apply (e : C ≌ D) [e.functor.CommShift ℤ]
    {X X' : C} {Y Y' : D} (hX : e.functor.obj X ≅ Y)
    (hY : e.functor.obj X' ≅ Y') (n : ℤ) (f : ShiftedHom X X' n) :
    e.shiftedHomMap hX hY n f =
      hX.inv ≫ ShiftedHom.map f e.functor ≫
        (shiftFunctor D n).map hY.hom := sorry

/-- An equivalence induces a bijection between shifted Hom sets after identifying both
endpoints. -/
theorem shiftedHomMap_bijective (e : C ≌ D) [e.functor.CommShift ℤ]
    {X X' : C} {Y Y' : D} (hX : e.functor.obj X ≅ Y)
    (hY : e.functor.obj X' ≅ Y') (n : ℤ) :
    Function.Bijective (e.shiftedHomMap hX hY n) := sorry

/-- Shifted-Hom transport by the identity equivalence is the identity. -/
@[simp]
theorem shiftedHomMap_refl (X X' : C) (n : ℤ) (f : ShiftedHom X X' n) :
    (Equivalence.refl : C ≌ C).shiftedHomMap
        (Iso.refl X) (Iso.refl X') n f = f := sorry

/-- Shifted-Hom transport respects composition of equivalences and endpoint
identifications. -/
theorem shiftedHomMap_trans
    {E : Type uE} [Category.{vE} E] [HasShift E ℤ]
    (e : C ≌ D) (e' : D ≌ E)
    [e.functor.CommShift ℤ] [e'.functor.CommShift ℤ]
    {X X' : C} {Y Y' : D} {Z Z' : E}
    (hX : e.functor.obj X ≅ Y) (hY : e.functor.obj X' ≅ Y')
    (kX : e'.functor.obj Y ≅ Z) (kY : e'.functor.obj Y' ≅ Z')
    (n : ℤ) (f : ShiftedHom X X' n) :
    (e.trans e').shiftedHomMap
        (e'.functor.mapIso hX ≪≫ kX) (e'.functor.mapIso hY ≪≫ kY) n f =
      e'.shiftedHomMap kX kY n (e.shiftedHomMap hX hY n f) := sorry

/-- Pull an identification of a forward image back to an identification from the chosen
quasi-inverse image. -/
@[stacks 09S9 "inverse endpoint identification for shifted Hom"]
def inverseObjIso (e : C ≌ D) {X : C} {Y : D}
    (h : e.functor.obj X ≅ Y) : e.inverse.obj Y ≅ X :=
  e.inverse.mapIso h.symm ≪≫ (e.unitIso.app X).symm

/-- The explicit inverse transport on shifted morphisms. -/
@[stacks 09S9 "inverse shifted Hom transport"]
noncomputable def shiftedHomInverseMap (e : C ≌ D) [e.functor.CommShift ℤ]
    {X X' : C} {Y Y' : D} (hX : e.functor.obj X ≅ Y)
    (hY : e.functor.obj X' ≅ Y') (n : ℤ) :
    ShiftedHom Y Y' n → ShiftedHom X X' n :=
  -- Local instance justification (instance diamond): mathlib exposes the canonical inverse
  -- shift structure as a `def`; keeping it local avoids competing with specialized inverses.
  letI := e.commShiftInverse ℤ
  e.inverse.shiftedHomMap (e.inverseObjIso hX) (e.inverseObjIso hY) n

/-- Shifted-Hom transport along an additive linear equivalence, bundled as a linear map. -/
@[stacks 09S9 "linear shifted Hom transport along an equivalence"]
noncomputable def shiftedHomLinearMap
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (e : C ≌ D) [e.functor.CommShift ℤ] [e.functor.Additive] [e.functor.Linear R]
    {X X' : C} {Y Y' : D} (hX : e.functor.obj X ≅ Y)
    (hY : e.functor.obj X' ≅ Y') (n : ℤ) :
    ShiftedHom X X' n →ₗ[R] ShiftedHom Y Y' n :=
  e.functor.shiftedHomLinearMapOfIsos hX hY n

/-- The explicit inverse shifted-Hom transport, bundled as a linear map. -/
@[stacks 09S9 "inverse linear shifted Hom transport along an equivalence"]
noncomputable def shiftedHomInverseLinearMap
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (e : C ≌ D) [e.functor.CommShift ℤ] [e.functor.Additive] [e.functor.Linear R]
    {X X' : C} {Y Y' : D} (hX : e.functor.obj X ≅ Y)
    (hY : e.functor.obj X' ≅ Y') (n : ℤ) :
    ShiftedHom Y Y' n →ₗ[R] ShiftedHom X X' n where
  toFun := e.shiftedHomInverseMap hX hY n
  map_add' := sorry
  map_smul' := sorry

/-- An additive linear equivalence induces a linear equivalence between arbitrary shifted Hom modules
after identifying both endpoints. -/
@[stacks 09S9 "shifted Hom linear equivalence"]
noncomputable def shiftedHomLinearEquiv
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (e : C ≌ D) [e.functor.CommShift ℤ] [e.functor.Additive] [e.functor.Linear R]
    {X X' : C} {Y Y' : D} (hX : e.functor.obj X ≅ Y)
    (hY : e.functor.obj X' ≅ Y') (n : ℤ) :
    ShiftedHom X X' n ≃ₗ[R] ShiftedHom Y Y' n where
  toFun := e.shiftedHomMap hX hY n
  invFun := e.shiftedHomInverseMap hX hY n
  map_add' := sorry
  map_smul' := sorry
  left_inv := sorry
  right_inv := sorry

/-- The linear shifted-Hom equivalence acts by the canonical shifted image, conjugated by the
chosen endpoint identifications. -/
@[simp]
theorem shiftedHomLinearEquiv_apply
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (e : C ≌ D) [e.functor.CommShift ℤ] [e.functor.Additive] [e.functor.Linear R]
    {X X' : C} {Y Y' : D} (hX : e.functor.obj X ≅ Y)
    (hY : e.functor.obj X' ≅ Y') (n : ℤ) (f : ShiftedHom X X' n) :
    e.shiftedHomLinearEquiv (R := R) hX hY n f =
      hX.inv ≫ ShiftedHom.map f e.functor ≫
        (shiftFunctor D n).map hY.hom := sorry

/-- The inverse of the linear shifted-Hom equivalence is the explicit quasi-inverse
transport. -/
@[simp]
theorem shiftedHomLinearEquiv_symm_apply
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (e : C ≌ D) [e.functor.CommShift ℤ] [e.functor.Additive] [e.functor.Linear R]
    {X X' : C} {Y Y' : D} (hX : e.functor.obj X ≅ Y)
    (hY : e.functor.obj X' ≅ Y') (n : ℤ) (f : ShiftedHom Y Y' n) :
    (e.shiftedHomLinearEquiv (R := R) hX hY n).symm f =
      e.shiftedHomInverseMap hX hY n f := sorry

end Equivalence

end CategoryTheory
