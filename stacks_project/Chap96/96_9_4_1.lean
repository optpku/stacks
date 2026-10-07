module

public import stacks_project.Chap96.«96_9_4_1_Comparison»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

/- 96.9.4.1: let `p : 𝒳 ⟶ (Sch/S)_fppf` be a category fibred in groupoids
and let `F` be an étale sheaf of `𝒪_𝒳`-modules. If `φ : x ⟶ y` is a morphism
of `𝒳` lying over `a : U ⟶ V`, the set-valued comparison is compatible with
`a_small^♯` and induces a comparison morphism
`c_φ : a_small^*(F|_{V_étale}) ⟶ F|_{U_étale}` of `𝒪_{U_étale}`-modules,
owned by `GroupoidsOver.moduleComparison`. -/
@[stacks 06WC] #check AlgebraicGeometry.GroupoidsOver.moduleComparison
