module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.FunctorialInjectives
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C]

/- Proposition 19.6.1: abelian presheaves on a category admit functorial injective embeddings.
The reusable owner is the canonical instance in
`ReasLib.CategoryTheory.Sites.AbelianSheaf.FunctorialInjectives`. -/
@[stacks 01DK] #check
  (inferInstance : HasFunctorialInjectives
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}))

#check @CategoryTheory.AbelianPresheaf.objectRestriction
#check @CategoryTheory.AbelianPresheaf.objectCorestriction
#check @CategoryTheory.AbelianPresheaf.Discrete.injectiveFunctor
#check @CategoryTheory.AbelianPresheaf.Discrete.injectiveι
