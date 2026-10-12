/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.FamilyMorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w₂ w₁ v u

variable {C : Type u} [Category.{v} C]

section morphismOfFamilies
variable {U V : C} (base : U ⟶ V)
variable (𝒰 : PreZeroHypercover.{w₁} U)
variable (𝒱 : PreZeroHypercover.{w₂} V)

/- Definition 7.8.1 (1): a morphism of families of maps with fixed target from
𝒰 = {Uᵢ ⟶ U} to 𝒱 = {Vⱼ ⟶ V} is given by a morphism U ⟶ V, a map of sets
α : I → J, and for each i a morphism Uᵢ ⟶ V_{α(i)} making the square commute. -/
@[stacks 00VT] #check
  (CategoryTheory.PreZeroHypercover.HomOver base 𝒰 𝒱 : Type (max w₁ w₂ v))

end morphismOfFamilies

section refinement
variable {U : C}
variable (𝒰 : PreZeroHypercover.{w₁} U)
variable (𝒱 : PreZeroHypercover.{w₂} U)

/- Definition 7.8.1 (2): when U = V and U ⟶ V is the identity, 𝒰 is a
refinement of the family 𝒱. -/
@[stacks 00VT] #check (CategoryTheory.PreZeroHypercover.Refines 𝒰 𝒱 : Prop)

end refinement
