/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms of locally constant sheaves

This leaf records when a morphism of sheaves is locally represented by morphisms between
constant models.  The chart predicate is separated from the covering predicate so downstream
arguments can work either over one object or over a chosen top cover.
-/

@[expose] public section

open CategoryTheory

universe u v w w'

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Hom

variable {D : Type w} [Category.{w'} D]
variable [∀ U : C, HasWeakSheafify (J.over U) D]

/-- A sheaf morphism is constant on `U`, with source models satisfying `P`, when its restriction
is identified with the constant-sheaf morphism induced by a morphism between two coefficient
objects. -/
def IsConstantOn (P : D → Prop) {F G : Sheaf J D} (φ : F ⟶ G) (U : C) : Prop :=
  ∃ (A B : D) (f : A ⟶ B)
      (eF : F.over U ≅ (constantSheaf (J.over U) D).obj A)
      (eG : G.over U ≅ (constantSheaf (J.over U) D).obj B),
    P A ∧ CommSq ((J.overPullback D U).map φ) eF.hom eG.hom
      ((constantSheaf (J.over U) D).map f)

/-- A direct witness characterization of a constant chart for a sheaf morphism. -/
theorem isConstantOn_iff (P : D → Prop) {F G : Sheaf J D} (φ : F ⟶ G) (U : C) :
    IsConstantOn P φ U ↔
      ∃ (A B : D) (f : A ⟶ B)
          (eF : F.over U ≅ (constantSheaf (J.over U) D).obj A)
          (eG : G.over U ≅ (constantSheaf (J.over U) D).obj B),
        P A ∧ CommSq ((J.overPullback D U).map φ) eF.hom eG.hom
          ((constantSheaf (J.over U) D).map f) := sorry

/-- A sheaf morphism has a constant-chart cover with source predicate `P` when some top cover
makes it constant on every member. -/
@[stacks 093S "constant-chart cover"]
def HasConstantChartCover (P : D → Prop) {F G : Sheaf J D} (φ : F ⟶ G) : Prop :=
  ∃ (I : Type (max u v)) (U : I → C), J.CoversTop U ∧
    ∀ i : I, IsConstantOn P φ (U i)

/-- A full witness characterization of a constant-chart cover, exposing the cover, both
constant models, their morphism, the chart isomorphisms, and the commuting square. -/
theorem hasConstantChartCover_iff (P : D → Prop) {F G : Sheaf J D} (φ : F ⟶ G) :
    HasConstantChartCover P φ ↔
      ∃ (I : Type (max u v)) (U : I → C), J.CoversTop U ∧
        ∀ i : I,
          ∃ (A B : D) (f : A ⟶ B)
              (eF : F.over (U i) ≅ (constantSheaf (J.over (U i)) D).obj A)
              (eG : G.over (U i) ≅ (constantSheaf (J.over (U i)) D).obj B),
            P A ∧ CommSq ((J.overPullback D (U i)).map φ) eF.hom eG.hom
              ((constantSheaf (J.over (U i)) D).map f) := sorry

end Hom

end CategoryTheory.Sheaf

open CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Types

variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]

/-- A morphism from a finite locally constant sheaf of types to a locally
constant sheaf admits a constant-chart cover with finite source models. -/
@[stacks 093S "(1)"]
theorem CategoryTheory.Sheaf.IsFiniteLocallyConstant.hom_hasConstantChartCover
    {F G : Sheaf J (Type w)} (φ : F ⟶ G)
    [IsFiniteLocallyConstant F] [IsLocallyConstant G] :
    Hom.HasConstantChartCover (fun A : Type w ↦ Finite A) φ := sorry

end Types

section AddCommGroups

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]

/-- A morphism from a finite locally constant sheaf of abelian groups to a
locally constant sheaf admits a constant-chart cover with finite source models. -/
@[stacks 093S "(2)"]
theorem CategoryTheory.Sheaf.IsFiniteLocallyConstantAddCommGrp.hom_hasConstantChartCover
    {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)
    [IsFiniteLocallyConstantAddCommGrp F] [IsLocallyConstant G] :
    Hom.HasConstantChartCover (fun A : AddCommGrpCat.{w} ↦ Finite A) φ := sorry

end AddCommGroups

section Modules

variable {Λ : Type w} [Ring Λ]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]

/-- A morphism from a finite-type locally constant sheaf of `Λ`-modules to a
locally constant sheaf admits a constant-chart cover with finite-type source models. -/
@[stacks 093S "(3)"]
theorem CategoryTheory.Sheaf.IsFiniteTypeLocallyConstantModule.hom_hasConstantChartCover
    {F G : Sheaf J (ModuleCat.{w} Λ)} (φ : F ⟶ G)
    [IsFiniteTypeLocallyConstantModule F] [IsLocallyConstant G] :
    Hom.HasConstantChartCover (fun M : ModuleCat.{w} Λ ↦ Module.Finite Λ M) φ := sorry

end Modules
