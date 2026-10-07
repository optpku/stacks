module

public import stacks_project.Chap96.Definition_96_24_1_Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 96.24.1: let `p : 𝒳 ⟶ (Sch/S)_fppf` be a category fibred in
groupoids. The associated affine site is the full subcategory `𝒳_affine` of
`𝒳` whose objects are those `x` lying over an affine scheme `U`. The topology
on `𝒳_affine` is the chaotic one, i.e. sheaves on `𝒳_affine` are the same as
presheaves. -/
@[stacks 0H09] #check @GroupoidsOver.Affine

/- The chaotic topology on the associated affine site. -/
@[stacks 0H09] #check @GroupoidsOver.affineTopology
