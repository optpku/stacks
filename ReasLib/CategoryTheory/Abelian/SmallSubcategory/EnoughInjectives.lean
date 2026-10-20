module

public import ReasLib.CategoryTheory.Abelian.SmallSubcategory
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

@[expose] public section

universe i w v u

open CategoryTheory

namespace CategoryTheory.SmallAbelianSubcategory

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]

/-- Every small object property in an abelian category with enough injectives is contained in a
small abelian full subcategory that also has enough injectives, and whose injective objects are
exactly the ambient injective objects. -/
theorem exists_containing_enoughInjectives (E : ObjectProperty A)
    [ObjectProperty.Small.{w} E] :
    ∃ B : SmallAbelianSubcategory.{max v w, v, u} A,
      B.Contains E ∧ EnoughInjectives B.FullSubcategory ∧
        ∀ Y : B.FullSubcategory, Injective Y ↔ Injective Y.obj := sorry

/-- Every set-sized family of objects in a possibly large abelian category with enough injectives
is contained in a small abelian full subcategory preserving injectivity. -/
theorem exists_containingFamily_enoughInjectives {I : Type i} [Small.{w} I] (X : I → A) :
    ∃ B : SmallAbelianSubcategory.{max v w, v, u} A,
      (∀ i, B.carrier (X i)) ∧ EnoughInjectives B.FullSubcategory ∧
        ∀ Y : B.FullSubcategory, Injective Y ↔ Injective Y.obj := sorry

end CategoryTheory.SmallAbelianSubcategory
