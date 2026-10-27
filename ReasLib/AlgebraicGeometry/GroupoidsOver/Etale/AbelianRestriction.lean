/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SmallEtaleComparison
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Restriction of abelian étale sheaves to a representing algebraic space

Continuous sheaf pushforward along the small étale comparison functor gives
restriction of abelian sheaves and preserves injective objects and K-injective complexes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite ComplexShape
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {F : AlgebraicSpace S} {X : GroupoidsOver S}

/-- Restriction of an abelian étale sheaf on `X` to the small étale site of a
representing algebraic space `F`, as `I |_{F_étale} = π_{F,*} I`. -/
abbrev restrictAbelian (e : F.toGroupoids ≌ X) :
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

/-- Restriction of abelian étale sheaves along a representing algebraic space
preserves injective objects. -/
instance restrictAbelian.instPreservesInjectiveObjects
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [HasSheafify (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u}] :
    (restrictAbelian e).PreservesInjectiveObjects := sorry

/-- Restriction from the étale site of an algebraic stack to a representing algebraic
space sends injective abelian sheaves to injective abelian sheaves. -/
theorem injective_restrictAbelian [AlgebraicStack X]
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [HasSheafify (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u}]
    (I : Sheaf X.etaleTopology AddCommGrpCat.{u}) [Injective I] :
    Injective ((restrictAbelian e).obj I) := sorry

/-- Restriction from the étale site of an algebraic stack to a representing algebraic
space sends K-injective cochain complexes of abelian sheaves to K-injective complexes. -/
instance isKInjective_restrictAbelian [AlgebraicStack X]
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [HasSheafify (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u}]
    (I : CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{u}) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((restrictAbelian e).mapHomologicalComplex (up ℤ)).obj I) := sorry

end AlgebraicGeometry.GroupoidsOver
