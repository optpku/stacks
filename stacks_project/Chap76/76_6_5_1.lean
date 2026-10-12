/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.«76_6_5_1_Comparison»
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

/- 76.6.5.1: the canonical surjection of graded algebras
`Sym(C_{Z/X}) ⟶ C_{Z/X,*}` induces a closed immersion of cones over `Z`,
displayed as `C_{Z/X} ⟶ N_{Z/X}`. -/
@[stacks 09RV]
#check (normalConeToNormalBundle i : normalCone i ⟶ normalBundle i)
