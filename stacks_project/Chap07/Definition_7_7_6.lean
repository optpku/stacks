/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Sheaf.Coyoneda
import StacksCheckRecall

@[expose] public section

universe uC vC uA vA

open CategoryTheory

variable {C : Type uC} [Category.{vC} C] {A : Type uA} [Category.{vA} A]
variable (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ A)

#check (CategoryTheory.Presheaf.IsSheaf J : (Cᵒᵖ ⥤ A) → Prop)

/- Definition 7.7.6: a presheaf `F` on a site `(C, J)` valued in a category `A` is a sheaf
iff for every object `X` of `A` the Hom-valued presheaf of types
`F_X := F ⋙ coyoneda.obj (op X)` is a sheaf of types. -/
@[stacks 00VR] #check
  (CategoryTheory.Presheaf.isSheaf_iff_forall_isSheaf_coyoneda J F :
    CategoryTheory.Presheaf.IsSheaf J F ↔
      ∀ object : A,
        CategoryTheory.Presieve.IsSheaf J
          (F ⋙ CategoryTheory.coyoneda.obj (Opposite.op object)))
