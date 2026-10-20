module

public import ReasLib.CategoryTheory.Sites.TypeSheafification
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open GrothendieckTopology

universe u v

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (F : Cᵒᵖ ⥤ Type (max u v))
variable (X : C)
variable (𝒢 : Sheaf J (Type (max u v)))

/- Theorem 59.13.2 (1): the plus construction is a presheaf, and its colimit is indexed by
the directed category opposite to the poset of covering sieves. -/
@[stacks 03NS] #check
  (CategoryTheory.GrothendieckTopology.TypeSheafification.plusObj J F :
    Cᵒᵖ ⥤ Type (max u v))

@[stacks 03NS] #check (inferInstance : IsFiltered (J.Cover X)ᵒᵖ)

/- Theorem 59.13.2 (2): the plus construction has a canonical map of presheaves
`F ⟶ J.plusObj F`. -/
@[stacks 03NS] #check
  (CategoryTheory.GrothendieckTopology.TypeSheafification.toPlus J F :
    F ⟶ J.plusObj F)

/- Theorem 59.13.2 (3): if `F` is separated, then its plus construction is a sheaf and the
canonical map is injective on sections over every object. -/
@[stacks 03NS] #check
  (CategoryTheory.GrothendieckTopology.plusObj_isSheaf_of_isSeparated J F :
    Presieve.IsSeparated J F → Presheaf.IsSheaf J (J.plusObj F))

@[stacks 03NS] #check
  (CategoryTheory.GrothendieckTopology.toPlus_injective_of_isSeparated J F :
    Presieve.IsSeparated J F →
      ∀ U : C, Function.Injective ((J.toPlus F).app (op U)))

/- Theorem 59.13.2 (4): the plus construction of every presheaf is separated. -/
@[stacks 03NS] #check
  (CategoryTheory.GrothendieckTopology.plusObj_isSeparated J F :
    Presieve.IsSeparated J (J.plusObj F))

/- Theorem 59.13.2 (5): the double-plus construction is a sheaf and is left adjoint to the
inclusion of sheaves, giving the functorial Hom equivalence against every sheaf `𝒢`. -/
@[stacks 03NS] #check
  (CategoryTheory.GrothendieckTopology.TypeSheafification.isSheaf_plus_plus J F :
    Presheaf.IsSheaf J (J.plusObj (J.plusObj F)))

@[stacks 03NS] #check
  (((CategoryTheory.plusPlusAdjunction J (Type (max u v))).homEquiv F 𝒢).symm :
    (F ⟶ (CategoryTheory.sheafToPresheaf J (Type (max u v))).obj 𝒢) ≃
      ((CategoryTheory.plusPlusSheaf J (Type (max u v))).obj F ⟶ 𝒢))
