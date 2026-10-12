/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelianYoneda.ULift
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

universe u v

noncomputable section

section

variable {C : Type u} [Category.{v} C]
variable (K : GrothendieckTopology C)
variable [HasWeakSheafify K AddCommGrpCat.{max u v}]
variable (X : C) (𝒢 : Sheaf K AddCommGrpCat.{max u v})

/- 19.7.2.1: morphisms from the free abelian sheaf on `X` to an abelian sheaf `𝒢`
correspond to sections of `𝒢` over `X`. This is the canonical weak-sheafification
free-abelian-representable Hom/evaluation equivalence. -/
@[stacks 05NY] #check
  (GrothendieckTopology.FreeAbelianYoneda.ULift.homEquiv.{u} X 𝒢 :
    (GrothendieckTopology.FreeAbelianYoneda.ULift.obj.{u} K X ⟶ 𝒢) ≃
      𝒢.obj.obj (op X))

/- Companion check: the source bijection statement is exactly the canonical bijectivity theorem
for the weak-sheafification equivalence above. -/
#check
  ((GrothendieckTopology.FreeAbelianYoneda.ULift.homEquiv.{u} X 𝒢).bijective :
    Function.Bijective
      (GrothendieckTopology.FreeAbelianYoneda.ULift.homEquiv.{u} X 𝒢))

end
