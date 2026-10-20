/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import stacks_project.Chap96.Lemma_96_10_1_Comparison

/-!
# Restriction of abelian étale sheaves along a representing algebraic space

An equivalence `e : F.toGroupoids ≌ X` induces the continuous functor
`u = smallEtaleFunctor F X e : F_étale ⥤ X`. Restriction of an abelian
étale sheaf on `X` to `F_étale` is continuous sheaf pushforward along `u`.
This is `I |_{F_étale}` on `Ab`, equivalently `π_{F,*} = i_F⁻¹`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {F : AlgebraicSpace S} {X : GroupoidsOver S}

/-- Restriction of an abelian étale sheaf on `X` to the small étale site of a
representing algebraic space `F`, as `I |_{F_étale} = π_{F,*} I`. -/
def restrictAbelian (e : F.toGroupoids ≌ X) :
    Sheaf X.etaleTopology AddCommGrpCat.{u} ⥤
      Sheaf (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u} :=
  (smallEtaleFunctor F X e).sheafPushforwardContinuous AddCommGrpCat.{u}
    (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology

variable (e : F.toGroupoids ≌ X)

/-- `restrictAbelian e` is continuous sheaf pushforward of abelian groups along
`smallEtaleFunctor F X e`. -/
theorem restrictAbelian_eq :
    restrictAbelian e =
      (smallEtaleFunctor F X e).sheafPushforwardContinuous AddCommGrpCat.{u}
        (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology :=
  rfl

/-- Sections of a restricted abelian sheaf over `U` étale over `F` are the
original sections on `u(U)`. -/
theorem restrictAbelian_obj (I : Sheaf X.etaleTopology AddCommGrpCat.{u})
    (U : AlgebraicSpace.smallEtaleSite F) :
    ((restrictAbelian e).obj I).obj.obj (op U) =
      I.obj.obj (op ((smallEtaleFunctor F X e).obj U)) :=
  rfl

/-- Restriction of abelian étale sheaves along a representing algebraic space is
an additive functor. -/
instance restrictAbelian.instAdditive : (restrictAbelian e).Additive :=
  sorry

/-- Restriction of abelian étale sheaves along a representing algebraic space
preserves injective objects. -/
instance restrictAbelian.instPreservesInjectiveObjects
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [HasSheafify (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u}] :
    (restrictAbelian e).PreservesInjectiveObjects :=
  sorry

end AlgebraicGeometry.GroupoidsOver
