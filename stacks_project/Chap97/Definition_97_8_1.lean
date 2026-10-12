/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap97.Definition_97_8_1_Algebraic
import StacksCheckRecall

@[expose] public section

/- Definition 97.8.1: a 1-morphism `F : X ⟶ Y` of stacks in groupoids over
`(Sch/S)_fppf` is algebraic if for every scheme `T` over `S` and every object
`ξ` of `Y` over `T` the 2-fibre product `(Sch/T)_fppf ×_{ξ, Y} X` is an
algebraic stack over `S`. -/
@[stacks 06CF] #check AlgebraicGeometry.Groupoids.Hom.Algebraic
