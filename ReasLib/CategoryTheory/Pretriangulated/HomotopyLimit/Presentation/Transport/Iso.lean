/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Iso
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Transport.Object
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Transport.Tower
import Mathlib.Tactic.CrossRefAttribute

/-!
# Compatible Isomorphisms from Transported Homotopy-Limit Presentations

Object and tower transport do more than preserve the homotopy-limit predicate: they produce
canonical compatible isomorphisms of presentations.  These builders expose the common
`Presentation.Iso` interface, hence also its stage and triangle APIs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u v

namespace CategoryTheory.HomotopyLimit

open SequentialInverseSystem.Milnor

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Presentation.ObjectIso

/-- Inclusion compatibility for the presentation isomorphism induced by object transport. -/
theorem presentationIso_ιComm {K : SequentialInverseSystem D} {X X' : D}
    (P : Presentation K X) (e : X ≅ X') :
    CommSq P.ι e.hom
      (ProductCone.map P.product (P.ofObjectIso e).product (𝟙 K))
      (P.ofObjectIso e).ι := sorry

/-- Connecting compatibility for the presentation isomorphism induced by object transport. -/
theorem presentationIso_connectingComm
    {K : SequentialInverseSystem D} {X X' : D}
    (P : Presentation K X) (e : X ≅ X') :
    CommSq P.connecting
      (ProductCone.map P.product (P.ofObjectIso e).product (𝟙 K))
      (e.hom⟦(1 : ℤ)⟧') (P.ofObjectIso e).connecting := sorry

/-- Object transport canonically yields a compatible isomorphism from the original
presentation to the transported presentation. -/
@[stacks 08TC]
def presentationIso {K : SequentialInverseSystem D} {X X' : D}
    (P : Presentation K X) (e : X ≅ X') :
    Presentation.Iso (CategoryTheory.Iso.refl K) P (P.ofObjectIso e) where
  iso := e
  ιComm := presentationIso_ιComm P e
  connectingComm := presentationIso_connectingComm P e

/-- The object component of the compatible isomorphism induced by object transport is the
supplied object isomorphism. -/
@[simp]
theorem presentationIso_iso {K : SequentialInverseSystem D} {X X' : D}
    (P : Presentation K X) (e : X ≅ X') :
    (presentationIso P e).iso = e := sorry

/-- The canonical stage maps before and after object transport are related by the supplied
object isomorphism. -/
@[reassoc]
theorem stageProjection_naturality {K : SequentialInverseSystem D} {X X' : D}
    (P : Presentation K X) (e : X ≅ X') (n : ℕ) :
    P.stageProjection n = e.hom ≫ (P.ofObjectIso e).stageProjection n := sorry

end Presentation.ObjectIso

namespace Presentation.TowerIso

/-- Inclusion compatibility for the presentation isomorphism induced by tower transport. -/
theorem presentationIso_ιComm {K L : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : LimitCone (Discrete.functor L.family)) :
    CommSq P.ι (𝟙 X)
      (ProductCone.map P.product (P.ofTowerIso e Q).product e.hom)
      (P.ofTowerIso e Q).ι := sorry

/-- Connecting compatibility for the presentation isomorphism induced by tower transport. -/
theorem presentationIso_connectingComm
    {K L : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : LimitCone (Discrete.functor L.family)) :
    CommSq P.connecting
      (ProductCone.map P.product (P.ofTowerIso e Q).product e.hom)
      ((𝟙 X)⟦(1 : ℤ)⟧') (P.ofTowerIso e Q).connecting := sorry

/-- Tower transport canonically yields a compatible presentation isomorphism whose object
component is the identity. -/
@[stacks 08TC]
def presentationIso {K L : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : LimitCone (Discrete.functor L.family)) :
    Presentation.Iso e P (P.ofTowerIso e Q) where
  iso := CategoryTheory.Iso.refl X
  ιComm := presentationIso_ιComm P e Q
  connectingComm := presentationIso_connectingComm P e Q

/-- The object component of the compatible isomorphism induced by tower transport is the
identity isomorphism. -/
@[simp]
theorem presentationIso_iso {K L : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : LimitCone (Discrete.functor L.family)) :
    (presentationIso P e Q).iso = CategoryTheory.Iso.refl X := sorry

end Presentation.TowerIso

end CategoryTheory.HomotopyLimit
