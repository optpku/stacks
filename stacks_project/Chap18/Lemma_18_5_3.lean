module

public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelian
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.PreservesSheafification AddCommGrpCat.free]
variable (G : Cᵒᵖ ⥤ Type (max u v))

/- Lemma 18.5.3 (03AC): free abelianization commutes with sheafification, up to the canonical
comparison isomorphism. -/
@[stacks 03AC]
#check (J.freeAbelianSheafComparisonIso G :
  (Sheaf.composeAndSheafify J AddCommGrpCat.free).obj
      ((presheafToSheaf J (Type (max u v))).obj G) ≅
    J.freeAbelianSheaf G)

end CategoryTheory
