module

public import Mathlib.CategoryTheory.Sites.Subcanonical

@[expose] public section

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.Subcanonical]

/-- The representable sheaf associated to an object of a subcanonical site is its
Yoneda presheaf, regarded as a sheaf. -/
def representableSheaf (U : C) : Sheaf J (Type v) :=
  J.yoneda.obj U

/-- The underlying presheaf of a representable sheaf is the Yoneda presheaf. -/
@[simp]
theorem representableSheaf_obj (U : C) :
    (J.representableSheaf U).obj = CategoryTheory.yoneda.obj U := rfl

end CategoryTheory.GrothendieckTopology
