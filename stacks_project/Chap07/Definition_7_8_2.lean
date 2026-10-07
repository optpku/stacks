module

public import ReasLib.CategoryTheory.Sites.Family.Covering
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open SemiRepresentableFamily.Over

universe w₂ w₁ v u

variable {C : Type u} [Category.{v} C] {U : C}
variable (𝒰 : SemiRepresentableFamily.Over.{w₁} U) (𝒱 : SemiRepresentableFamily.Over.{w₂} U)

/- Definition 7.8.2 (1): two families of morphisms with fixed target 𝒰 and 𝒱
are combinatorially equivalent if there exist reindexings
α : 𝒰.index → 𝒱.index and β : 𝒱.index → 𝒰.index such that the displayed
arrows in Over U agree, i.e. 𝒰.obj i = 𝒱.obj (α i) and 𝒱.obj j = 𝒰.obj (β j). -/
@[stacks 00VU] #check CombinatoriallyEquivalent 𝒰 𝒱

/- Definition 7.8.2 (2): two families of morphisms with fixed target 𝒰 and 𝒱
are tautologically equivalent if there exist Hom maps both ways whose
component maps are isomorphisms in the slice Over U, equivalently commuting
triangles over U with isomorphisms as horizontal arrows. -/
@[stacks 00VU] #check TautologicallyEquivalent 𝒰 𝒱
