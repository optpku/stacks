/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.«91_7_1_2_Diagram»
import StacksCheckRecall

open CategoryTheory
open TopCat.Sheaf.FirstOrderThickening

universe u

/- 91.7.1.2: after identifying underlying spaces of first-order thickenings, a
commutative diagram of sheaves of rings on a space X, with front and back solutions
0 ⟶ 𝒢ⱼ ⟶ 𝒪_{X'ⱼ} ⟶ 𝒪_{Xⱼ} ⟶ 0 over 0 ⟶ 𝒥ⱼ ⟶ 𝒪_{S'ⱼ} ⟶ 𝒪_{Sⱼ} ⟶ 0,
vertical maps cⱼ, structure maps, a given g-map ν : 𝒢₁ ⟶ 𝒢₂, and with no filler
𝒪_{X'₁} ⟶ 𝒪_{X'₂}. -/
@[stacks 08UA] #check RelativeDiagram
#check RelativeDiagram.of
#check RelativeDiagram.spec
#check RelativeDiagram.c
#check RelativeDiagram.Fits
