module

public import ReasLib.CategoryTheory.Sites.Family
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] (U : C)

/- Definition 7.6.1: in a category C, a family of morphisms with fixed target is
an object U of C, an index type I (possibly empty), and morphisms Uᵢ ⟶ U for
each i ∈ I, written {Uᵢ ⟶ U}_{i ∈ I}. This is SemiRepresentableFamily.Over U,
with index = I and obj i the slice object of Uᵢ ⟶ U. The constructor ofArrows
packages the textbook tuple (I, Uᵢ, π). -/
@[stacks 0396] #check SemiRepresentableFamily.Over.{w} U

#check @SemiRepresentableFamily.Over.ofArrows
