module

public import stacks_project.Chap71.Definition_71_17_1_Blowup
public import stacks_project.Chap71.Definition_71_17_1_Rees
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

/- Definition 71.17.1: for a scheme `S`, an algebraic space `X` over `S`, and a
quasi-coherent ideal sheaf `I ⊂ 𝒪_X` with corresponding closed subspace `Z`, the
blowing up of `X` along `Z` (equivalently, the blowing up of `X` in `I`) is the
morphism `b : Proj_X (⊕_{n ≥ 0} I ^ n) ⟶ X` packaged as a chosen
`Blowup X I`; its exceptional divisor is `b⁻¹(Z)`, and `Z` is the center. -/
@[stacks 085Q] #check AlgebraicGeometry.AlgebraicSpace.Blowup

#check reesAlgebra

#check Blowup.center

#check Blowup.exceptionalDivisor

#check Blowup.along
