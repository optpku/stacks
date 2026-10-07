module

public import stacks_project.Chap90.Definition_90_7_3_FormalObject
import StacksCheckRecall

@[expose] public section

/- Definition 90.7.1 (1): a formal object of a category F cofibered in groupoids
over C_Λ is a triple ξ = (R, ξ_n, f_n) with R an object of hat C_Λ, objects
ξ_n of F over the truncations R ⧸ m_R^n, and morphisms f_n : ξ_{n+1} ⟶ ξ_n
lying over the truncation projections. This is owned by FormalObject. -/
@[stacks 06H3] #check FormalObject

/- Definition 90.7.1 (2): a morphism a : ξ ⟶ η of formal objects consists of
a map a_0 : R ⟶ S in hat C_Λ and morphisms a_n : ξ_n ⟶ η_n of F lying over
the induced truncations R ⧸ m_R^n ⟶ S ⧸ m_S^n, such that the successor
squares commute. This is owned by FormalObject.Hom. -/
@[stacks 06H3] #check FormalObject.Hom

#check FormalObject.category
