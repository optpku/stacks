/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap86.«86_7_0_1_Pullback»
public import stacks_project.Chap86.«86_7_0_1_Comparison»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

noncomputable section

universe u

/- 86.7.0.1: for a morphism `f : X ⟶ Y` of quasi-compact quasi-separated algebraic spaces over
a scheme `S`, a right adjoint `a` to `Rf_*`, and `K : DerivedQCoh Y`, the projection formula and
the counit define the canonical map `Lf^*K ⊗ a(𝒪_Y) ⟶ a(K)`. -/
@[stacks 0E5P] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pullbackTensorDualityMap :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (aAdjunction : pushforwardCohomologyIn f ⊣ a)
      (K : DerivedQCoh Y),
      tensorObj ((pullback f).obj K) (a.obj (structureSheaf Y)) ⟶ a.obj K)
