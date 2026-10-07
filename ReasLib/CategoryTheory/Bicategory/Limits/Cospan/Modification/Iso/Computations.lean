module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Iso.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Component computations for cospan modification isomorphisms

This leaf exposes the six component readouts for `CospanTransform.Hom.isoMk`. Consumers that
only construct the isomorphism can remain at `Iso.Construction`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

universe w v u

namespace CategoryTheory.Bicategory.CospanTransform.Hom

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}
variable {ψ φ : CospanTransform f g f' g'}

/-- The left component of the forward modification of `isoMk` is the supplied forward cell. -/
@[simp]
theorem isoMk_hom_left
    (leftIso : ψ.left ≅ φ.left) (rightIso : ψ.right ≅ φ.right)
    (baseIso : ψ.base ≅ φ.base)
    (leftNaturality :
      leftIso.hom ▷ f' ≫ φ.leftIso.hom =
        ψ.leftIso.hom ≫ f ◁ baseIso.hom)
    (rightNaturality :
      rightIso.hom ▷ g' ≫ φ.rightIso.hom =
        ψ.rightIso.hom ≫ g ◁ baseIso.hom) :
    left (isoMk leftIso rightIso baseIso leftNaturality rightNaturality).hom =
      leftIso.hom := sorry

/-- The right component of the forward modification of `isoMk` is the supplied forward cell. -/
@[simp]
theorem isoMk_hom_right
    (leftIso : ψ.left ≅ φ.left) (rightIso : ψ.right ≅ φ.right)
    (baseIso : ψ.base ≅ φ.base)
    (leftNaturality :
      leftIso.hom ▷ f' ≫ φ.leftIso.hom =
        ψ.leftIso.hom ≫ f ◁ baseIso.hom)
    (rightNaturality :
      rightIso.hom ▷ g' ≫ φ.rightIso.hom =
        ψ.rightIso.hom ≫ g ◁ baseIso.hom) :
    right (isoMk leftIso rightIso baseIso leftNaturality rightNaturality).hom =
      rightIso.hom := sorry

/-- The base component of the forward modification of `isoMk` is the supplied forward cell. -/
@[simp]
theorem isoMk_hom_base
    (leftIso : ψ.left ≅ φ.left) (rightIso : ψ.right ≅ φ.right)
    (baseIso : ψ.base ≅ φ.base)
    (leftNaturality :
      leftIso.hom ▷ f' ≫ φ.leftIso.hom =
        ψ.leftIso.hom ≫ f ◁ baseIso.hom)
    (rightNaturality :
      rightIso.hom ▷ g' ≫ φ.rightIso.hom =
        ψ.rightIso.hom ≫ g ◁ baseIso.hom) :
    base (isoMk leftIso rightIso baseIso leftNaturality rightNaturality).hom =
      baseIso.hom := sorry

/-- The left component of the inverse modification of `isoMk` is the supplied inverse cell. -/
@[simp]
theorem isoMk_inv_left
    (leftIso : ψ.left ≅ φ.left) (rightIso : ψ.right ≅ φ.right)
    (baseIso : ψ.base ≅ φ.base)
    (leftNaturality :
      leftIso.hom ▷ f' ≫ φ.leftIso.hom =
        ψ.leftIso.hom ≫ f ◁ baseIso.hom)
    (rightNaturality :
      rightIso.hom ▷ g' ≫ φ.rightIso.hom =
        ψ.rightIso.hom ≫ g ◁ baseIso.hom) :
    left (isoMk leftIso rightIso baseIso leftNaturality rightNaturality).inv =
      leftIso.inv := sorry

/-- The right component of the inverse modification of `isoMk` is the supplied inverse cell. -/
@[simp]
theorem isoMk_inv_right
    (leftIso : ψ.left ≅ φ.left) (rightIso : ψ.right ≅ φ.right)
    (baseIso : ψ.base ≅ φ.base)
    (leftNaturality :
      leftIso.hom ▷ f' ≫ φ.leftIso.hom =
        ψ.leftIso.hom ≫ f ◁ baseIso.hom)
    (rightNaturality :
      rightIso.hom ▷ g' ≫ φ.rightIso.hom =
        ψ.rightIso.hom ≫ g ◁ baseIso.hom) :
    right (isoMk leftIso rightIso baseIso leftNaturality rightNaturality).inv =
      rightIso.inv := sorry

/-- The base component of the inverse modification of `isoMk` is the supplied inverse cell. -/
@[simp]
theorem isoMk_inv_base
    (leftIso : ψ.left ≅ φ.left) (rightIso : ψ.right ≅ φ.right)
    (baseIso : ψ.base ≅ φ.base)
    (leftNaturality :
      leftIso.hom ▷ f' ≫ φ.leftIso.hom =
        ψ.leftIso.hom ≫ f ◁ baseIso.hom)
    (rightNaturality :
      rightIso.hom ▷ g' ≫ φ.rightIso.hom =
        ψ.rightIso.hom ≫ g ◁ baseIso.hom) :
    base (isoMk leftIso rightIso baseIso leftNaturality rightNaturality).inv =
      baseIso.inv := sorry

end CategoryTheory.Bicategory.CospanTransform.Hom
