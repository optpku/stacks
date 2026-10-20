module

public import ReasLib.CategoryTheory.Abelian.SmallSubcategory.EnoughInjectives
import StacksCheckRecall

@[expose] public section

universe i w v u

open CategoryTheory

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
variable {I : Type i} [Small.{w} I] (X : I → A)

/- Lemma 3.12.1 -/
@[stacks 0010] #check
  (CategoryTheory.SmallAbelianSubcategory.exists_containingFamily_enoughInjectives (A := A) X :
      ∃ B : SmallAbelianSubcategory.{max v w, v, u} A,
        (∀ i, B.carrier (X i)) ∧
          EnoughInjectives B.FullSubcategory ∧
            ∀ Y : B.FullSubcategory, Injective Y ↔ Injective Y.obj)

end CategoryTheory
