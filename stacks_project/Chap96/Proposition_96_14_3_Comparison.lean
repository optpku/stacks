/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Quotient
public import stacks_project.Chap78.Lemma_78_12_3_QCoh
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap96.Lemma_96_11_2_Pullback
public import stacks_project.Chap96.Lemma_96_13_2
public import stacks_project.Chap96.Lemma_96_14_2

/-! # Pullback coherence and the quotient atlas action -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver AlgebraicGeometry.GroupoidAlgebraicSpace
open scoped Bicategory
universe u

#check (AlgebraicGeometry.GroupoidsOver.QCoh.pullbackIso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} {f g : X ⟶ Y} (e : f ≅ g),
    QCoh.pullback g ≅ QCoh.pullback f)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.pullback_comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z),
    QCoh.pullback (f ≫ g) ≅ QCoh.pullback g ⋙ QCoh.pullback f)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.pullbackMap :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} {f g : X ⟶ Y} (α : f ⟶ g),
    QCoh.pullback g ⟶ QCoh.pullback f)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.action :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (F : QCoh (SmallQuotient.quotientStack G)),
    (AlgebraicSpace.QCoh.pullback G.t.left).obj (QCoh.atlasRestrict G F) ⟶
      (AlgebraicSpace.QCoh.pullback G.s.left).obj (QCoh.atlasRestrict G F))
