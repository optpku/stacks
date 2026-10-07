module

public import ReasLib.CategoryTheory.Sites.Family.Covering
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w₂ w₁ v u

variable {C : Type u} [Category.{v} C]

section morphismOfFamilies
variable {U V : C} (base : U ⟶ V)
variable (𝒰 : SemiRepresentableFamily.Over.{w₁} U)
variable (𝒱 : SemiRepresentableFamily.Over.{w₂} V)

/- Definition 7.8.1 (1): a morphism of families of maps with fixed target from
𝒰 = {Uᵢ ⟶ U} to 𝒱 = {Vⱼ ⟶ V} is given by a morphism U ⟶ V, a map of sets
α : I → J, and for each i a morphism Uᵢ ⟶ V_{α(i)} making the square commute. -/
@[stacks 00VT "(1)"] #check SemiRepresentableFamily.Over.Hom
  (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱

end morphismOfFamilies

#check @SemiRepresentableFamily.Over.map
#check @SemiRepresentableFamily.Over.Hom.map_hom
#check @SemiRepresentableFamily.Over.Hom.map_hom_id

section refinement
variable {U : C}
variable (𝒰 : SemiRepresentableFamily.Over.{w₁} U)
variable (𝒱 : SemiRepresentableFamily.Over.{w₂} U)

/- Definition 7.8.1 (2): when U = V and U ⟶ V is the identity, 𝒰 is a
refinement of the family 𝒱. -/
@[stacks 00VT "(2)"] #check SemiRepresentableFamily.Over.Refines 𝒰 𝒱

end refinement
