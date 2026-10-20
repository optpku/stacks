/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Whiskering Homotopies of Homological Complexes

This module packages simultaneous precomposition and postcomposition of a homotopy. Mathlib
already provides the one-sided operations Homotopy.compLeft and Homotopy.compRight; the
combined operation here is useful when a construction is functorial on both source and target.

It also packages transport through an explicit natural split monomorphism. The chosen retraction
remains data instead of being selected from a proposition-valued `IsSplitMono` instance.

@stack 010W
@stack 0112
@stack 09JP
-/

open CategoryTheory HomologicalComplex

universe w v u x z

namespace CategoryTheory.SplitMono

variable {J : Type x} [Category.{z} J]
variable {E : Type u} [Category.{v} E]
variable {Q F : J ⥤ E} {section_ : Q ⟶ F}

/-- A functor map factors through a natural split monomorphism and its chosen retraction. -/
@[reassoc]
theorem map_eq_factorization (s : SplitMono section_) {X Y : J} (f : X ⟶ Y) :
    Q.map f = (section_.app X ≫ F.map f) ≫ s.retraction.app Y := sorry

end CategoryTheory.SplitMono

namespace Homotopy

variable {ι : Type w} {V : Type u} [Category.{v} V] [Preadditive V]
variable {c : ComplexShape ι}
variable {A B C D : HomologicalComplex V c}
variable {a : A ⟶ B} {f g : B ⟶ C} {b : C ⟶ D}
variable {J : Type x} [Category.{z} J]
variable {Q F : J ⥤ HomologicalComplex V c} {section_ : Q ⟶ F}

/-- Simultaneously precompose and postcompose a homotopy of homological complexes. -/
@[stacks 010W "whiskering chain homotopies", stacks 0112 "whiskering cochain homotopies",
  stacks 09JP "whiskering homotopies of differential graded modules"]
def whisker (a : A ⟶ B) (h : Homotopy f g) (b : C ⟶ D) :
    Homotopy ((a ≫ f) ≫ b) ((a ≫ g) ≫ b) :=
  (h.compLeft a).compRight b

/-- The (i, j) component of a whiskered homotopy is the corresponding triple composite. -/
@[stacks 010W "components of whiskered chain homotopies", stacks 0112 "components of whiskered cochain homotopies", simp]
theorem whisker_hom (a : A ⟶ B) (h : Homotopy f g) (b : C ⟶ D) (i j : ι) :
    (whisker a h b).hom i j = a.f i ≫ h.hom i j ≫ b.f j := sorry

/-- Transport a homotopy through an explicit natural split monomorphism. -/
@[stacks 010W "homotopy transport through a natural split retract"]
noncomputable def ofSplitMono {X Y : J} {f g : X ⟶ Y}
    (s : SplitMono section_) (h : Homotopy (F.map f) (F.map g)) :
    Homotopy (Q.map f) (Q.map g) :=
  (Homotopy.ofEq (CategoryTheory.SplitMono.map_eq_factorization s f)).trans
    ((whisker (section_.app X) h (s.retraction.app Y)).trans
      (Homotopy.ofEq (CategoryTheory.SplitMono.map_eq_factorization s g).symm))

/-- The component formula for homotopy transport through a natural split retract. -/
@[simp, stacks 010W "components of split-retract homotopy transport"]
theorem ofSplitMono_hom {X Y : J} {f g : X ⟶ Y}
    (s : SplitMono section_) (h : Homotopy (F.map f) (F.map g)) (i j : ι) :
    (ofSplitMono s h).hom i j =
      (section_.app X).f i ≫ h.hom i j ≫ (s.retraction.app Y).f j := sorry

end Homotopy
