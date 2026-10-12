/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap69.Lemma_69_15_2_FinitePresentation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 69.15.2: let `S` be a scheme. Let `f : X ⟶ Y` be an affine morphism of algebraic spaces
over `S` with `Y` Noetherian. Then every quasi-coherent `𝒪_X`-module is a filtered colimit of
finitely presented `𝒪_X`-modules. -/
@[stacks 07UW] #check
  (isFinitePresentation_ind :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f] [IsNoetherian Y]
      (F : X.Modules) [F.IsQuasicoherent],
      (SheafOfModules.isFinitePresentation (structureSheaf X)).ind.{u} F)
