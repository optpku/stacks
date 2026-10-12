/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap105.Definition_105_4_3_Smooth
import StacksCheckRecall

@[expose] public section

/- Definition 105.4.3: a morphism `S ⟶ ℳ_{1,1}` is smooth if for every
morphism `S' ⟶ ℳ_{1,1}` the projection `S ×_{ℳ_{1,1}} S' ⟶ S'` is a
smooth morphism of schemes. The same pattern applies to other morphism
properties and other moduli stacks. -/
@[stacks 072P] #check AlgebraicGeometry.Groupoids.Hom.SmoothOnSchemes
