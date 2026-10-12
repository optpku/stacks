/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import stacks_project.Chap96.Lemma_96_12_3_Pullback
public import stacks_project.Chap103.Lemma_103_10_1

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
  [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)

def LQCohFbc.inverseImage : LQCohFbc Y ⥤ LQCohFbc X :=
  (lqcohFbc X).lift (LQCohFbc.inclusion Y ⋙ moduleInverseImage f) (fun _ ↦ sorry)

def QCoh.toLQCohFbc_pullback_app (G : QCoh Y) :
    (QCoh.toLQCohFbc X).obj ((QCoh.pullback f).obj G) ⟶
      (LQCohFbc.inverseImage f).obj ((QCoh.toLQCohFbc Y).obj G) :=
  homMk (𝟙 _)

def QCoh.toLQCohFbc_pullback_app_inv (G : QCoh Y) :
    (LQCohFbc.inverseImage f).obj ((QCoh.toLQCohFbc Y).obj G) ⟶
      (QCoh.toLQCohFbc X).obj ((QCoh.pullback f).obj G) :=
  homMk (𝟙 _)

def LQCohFbc.toQCoh_pullback_app
    (adjX : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X)
    (adjY : QCoh.toLQCohFbc Y ⊣ LQCohFbc.toQCoh Y)
    (F : LQCohFbc Y) :
    (QCoh.pullback f).obj ((LQCohFbc.toQCoh Y).obj F) ⟶
      (LQCohFbc.toQCoh X).obj ((LQCohFbc.inverseImage f).obj F) :=
  (adjX.homEquiv _ _).symm
    (QCoh.toLQCohFbc_pullback_app f ((LQCohFbc.toQCoh Y).obj F) ≫
      (LQCohFbc.inverseImage f).map (adjY.counit.app F))
