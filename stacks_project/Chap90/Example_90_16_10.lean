module

public import Mathlib.CategoryTheory.Elements
public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
public import stacks_project.Chap90.Example_90_16_10_ResidueHom
public import stacks_project.Chap90.Remark_90_6_3_PredeformationFunctor

/-!
# Prorepresentable functors are deformation functors

A prorepresentable functor on `ArtinianLocalAlgCat Λ k` is a deformation functor:
the associated cofibered set is a deformation category.
-/

@[expose] public section

open CategoryTheory CategoryOfElements

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- Example 90.16.10: a prorepresentable functor `F : ArtinianLocalAlgCat Λ k ⥤ Type u`
is a deformation functor, in the sense that the associated cofibered set
`CategoryOfElements.π F` is a deformation category. -/
@[stacks 06JB]
instance instIsDeformationCategory_π
    {F : ArtinianLocalAlgCat Λ k ⥤ Type u} [IsProrepresentable F] :
    IsDeformationCategory (π F) := sorry

/-- A prorepresentable functor is a predeformation functor: its value at the residue
field is a singleton. -/
instance instIsPredeformationFunctor_of_isProrepresentable
    {F : ArtinianLocalAlgCat Λ k ⥤ Type u} [IsProrepresentable F] :
    IsPredeformationFunctor F := sorry

end CategoryTheory.Functor
