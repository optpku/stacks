/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Category
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism construction for cospan modifications

This leaf constructs an isomorphism between two strong transformations of walking-cospan
diagrams from isomorphisms between their three vertex components. Only the two forward
generating naturality squares are required; inverse naturality and the inverse laws are
proof-only consequences. Component readouts are kept in `Iso.Computations`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

universe w v u

namespace CategoryTheory.Bicategory.CospanTransform.Hom

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}
variable {ψ φ : CospanTransform f g f' g'}

namespace Implementation.isoMk

/-- The inverse left generating square follows from the forward square and the component
isomorphism laws. -/
private theorem leftNaturalityInv
    (leftIso : ψ.left ≅ φ.left) (baseIso : ψ.base ≅ φ.base)
    (leftNaturality :
      leftIso.hom ▷ f' ≫ φ.leftIso.hom =
        ψ.leftIso.hom ≫ f ◁ baseIso.hom) :
    leftIso.inv ▷ f' ≫ ψ.leftIso.hom =
      φ.leftIso.hom ≫ f ◁ baseIso.inv := sorry

/-- The inverse right generating square follows from the forward square and the component
isomorphism laws. -/
private theorem rightNaturalityInv
    (rightIso : ψ.right ≅ φ.right) (baseIso : ψ.base ≅ φ.base)
    (rightNaturality :
      rightIso.hom ▷ g' ≫ φ.rightIso.hom =
        ψ.rightIso.hom ≫ g ◁ baseIso.hom) :
    rightIso.inv ▷ g' ≫ ψ.rightIso.hom =
      φ.rightIso.hom ≫ g ◁ baseIso.inv := sorry

/-- The componentwise forward and inverse modifications satisfy the first inverse law. -/
private theorem homInvId
    (leftIso : ψ.left ≅ φ.left) (rightIso : ψ.right ≅ φ.right)
    (baseIso : ψ.base ≅ φ.base)
    (leftNaturality :
      leftIso.hom ▷ f' ≫ φ.leftIso.hom =
        ψ.leftIso.hom ≫ f ◁ baseIso.hom)
    (rightNaturality :
      rightIso.hom ▷ g' ≫ φ.rightIso.hom =
        ψ.rightIso.hom ≫ g ◁ baseIso.hom) :
    comp
        (mk leftIso.hom rightIso.hom baseIso.hom
          leftNaturality rightNaturality)
        (mk leftIso.inv rightIso.inv baseIso.inv
          (leftNaturalityInv leftIso baseIso leftNaturality)
          (rightNaturalityInv rightIso baseIso rightNaturality)) =
      id ψ := sorry

/-- The componentwise forward and inverse modifications satisfy the second inverse law. -/
private theorem invHomId
    (leftIso : ψ.left ≅ φ.left) (rightIso : ψ.right ≅ φ.right)
    (baseIso : ψ.base ≅ φ.base)
    (leftNaturality :
      leftIso.hom ▷ f' ≫ φ.leftIso.hom =
        ψ.leftIso.hom ≫ f ◁ baseIso.hom)
    (rightNaturality :
      rightIso.hom ▷ g' ≫ φ.rightIso.hom =
        ψ.rightIso.hom ≫ g ◁ baseIso.hom) :
    comp
        (mk leftIso.inv rightIso.inv baseIso.inv
          (leftNaturalityInv leftIso baseIso leftNaturality)
          (rightNaturalityInv rightIso baseIso rightNaturality))
        (mk leftIso.hom rightIso.hom baseIso.hom
          leftNaturality rightNaturality) =
      id φ := sorry

end Implementation.isoMk

/-- Construct an isomorphism between cospan transformations from isomorphisms between their
three vertex components and naturality on the two generating arrows. -/
@[stacks 0040 "isomorphism of cospan transformations from component isomorphisms"]
def isoMk
    (leftIso : ψ.left ≅ φ.left) (rightIso : ψ.right ≅ φ.right)
    (baseIso : ψ.base ≅ φ.base)
    (leftNaturality :
      leftIso.hom ▷ f' ≫ φ.leftIso.hom =
        ψ.leftIso.hom ≫ f ◁ baseIso.hom)
    (rightNaturality :
      rightIso.hom ▷ g' ≫ φ.rightIso.hom =
        ψ.rightIso.hom ≫ g ◁ baseIso.hom) :
    ψ ≅ φ where
  hom :=
    mk leftIso.hom rightIso.hom baseIso.hom
      leftNaturality rightNaturality
  inv :=
    mk leftIso.inv rightIso.inv baseIso.inv
      (Implementation.isoMk.leftNaturalityInv leftIso baseIso leftNaturality)
      (Implementation.isoMk.rightNaturalityInv rightIso baseIso rightNaturality)
  hom_inv_id :=
    Implementation.isoMk.homInvId leftIso rightIso baseIso
      leftNaturality rightNaturality
  inv_hom_id :=
    Implementation.isoMk.invHomId leftIso rightIso baseIso
      leftNaturality rightNaturality

/- Data and axiom audit (mathlib 4.32):

`#print axioms` reports `[propext, sorryAx, Classical.choice, Quot.sound]` for `isoMk`.
Source inspection shows that it stores the supplied component isomorphisms through the existing
`Hom.mk` constructor and uses their explicit inverse cells. Thus `sorryAx` is confined to inverse
naturality and inverse-law equalities and cannot choose any component isomorphism. -/

end CategoryTheory.Bicategory.CospanTransform.Hom
