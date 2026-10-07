module

public import stacks_project.Chap81.«81_10_6_2_Reverse»
public import stacks_project.Chap81.«81_10_6_2_Square»
import StacksCheckRecall

open AlgebraicGeometry.AlgebraicSpace.Modules

/- 81.10.6.2: In Situation 81.10.5, to a triple (H, G, φ) one assigns the
𝒪_X-module Ker(j_* H ⊕ f_* G ⟶ (f ∘ j')_* (G|_V)), where j : U = X \ Z ⟶ X,
j' : V = Y \ f⁻¹(Z) ⟶ Y, and φ : (f|_V)^* H ⟶ G|_V. -/
@[stacks 0AEX] #check FormalGlueing.reverse
