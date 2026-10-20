/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.AddCommGrp.Monoidal
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian

@[expose] public section

open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Sheafification equivalences of abelian presheaves are stable under integer tensor. -/
instance abelianTensorIsMonoidal : (J.W (A := AddCommGrpCat.{w})).IsMonoidal :=
  sorry

/-- Integer tensor on abelian sheaves is induced by monoidal sheafification. -/
instance abelianTensorMonoidalCategory : MonoidalCategory (Sheaf J AddCommGrpCat.{w}) :=
  Sheaf.monoidalCategory J AddCommGrpCat.{w}

/-- Integer tensor of abelian sheaves is additive in both variables. -/
instance abelianTensorMonoidalPreadditive :
    MonoidalPreadditive (Sheaf J AddCommGrpCat.{w}) :=
  sorry

/-- Tensor of abelian sheaves is the sheafification of pointwise integer tensor. -/
def abelianTensorIsoSheafify (F G : Sheaf J AddCommGrpCat.{w}) :
    F ⊗ G ≅ (presheafToSheaf J AddCommGrpCat.{w}).obj (F.obj ⊗ G.obj) :=
  ((asIso ((sheafificationAdjunction J AddCommGrpCat.{w}).counit.app F)).symm ⊗ᵢ
    (asIso ((sheafificationAdjunction J AddCommGrpCat.{w}).counit.app G)).symm) ≪≫
      Functor.Monoidal.μIso (presheafToSheaf J AddCommGrpCat.{w}) F.obj G.obj

/-- The unit of integer tensor on abelian sheaves is the constant integer sheaf. -/
def abelianTensorUnitIsoInteger :
    𝟙_ (Sheaf J AddCommGrpCat.{w}) ≅ constantIntegerSheaf J :=
  Functor.Monoidal.εIso (presheafToSheaf J AddCommGrpCat.{w}) ≪≫
    (presheafToSheaf J AddCommGrpCat.{w}).mapIso
      ((Functor.const Cᵒᵖ).mapIso AddCommGrpCat.tensorUnitIsoInteger)

end CategoryTheory.Sheaf
