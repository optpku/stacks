module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Constructors for bicategorical cospan modifications

This leaf owns the explicit finite walking-cospan assembly behind `CospanTransform.Hom.mk`. Its
inputs are exactly the three vertex `2`-cells and the two generating naturality equations. The
projection, identity, and composition computations are kept in `Modification.Computations`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.CospanTransform.Hom

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}
variable {ψ φ : CospanTransform f g f' g'}

namespace Implementation

/- Implementation boundary: the finite walking-cospan case split is confined here. Public
users consume the three vertex cells and two generator equations supplied to `mk`. -/

/-- Assemble a modification's object components from its three vertex components. -/
private def app
    (left : ψ.left ⟶ φ.left) (right : ψ.right ⟶ φ.right)
    (base : ψ.base ⟶ φ.base) :
    ∀ a : LocallyDiscrete Limits.WalkingCospan, ψ.app a ⟶ φ.app a
  | ⟨none⟩ => base
  | ⟨some Limits.WalkingPair.left⟩ => left
  | ⟨some Limits.WalkingPair.right⟩ => right

/-- The two generating squares imply modification naturality on every walking-cospan arrow. -/
private theorem naturality
    (left : ψ.left ⟶ φ.left) (right : ψ.right ⟶ φ.right)
    (base : ψ.base ⟶ φ.base)
    (leftNaturality :
      left ▷ f' ≫ φ.leftIso.hom = ψ.leftIso.hom ≫ f ◁ base)
    (rightNaturality :
      right ▷ g' ≫ φ.rightIso.hom = ψ.rightIso.hom ≫ g ◁ base) :
    ∀ {a b : LocallyDiscrete Limits.WalkingCospan} (h : a ⟶ b),
      (cospan f g).map h ◁ app left right base b ≫ (φ.naturality h).hom =
        (ψ.naturality h).hom ≫
          app left right base a ▷ (cospan f' g').map h := sorry

end Implementation

/-- Construct a modification from its three vertex cells and the two generating naturality
squares. All non-`Prop` component data are explicit. -/
@[stacks 0040 "constructor for a bicategorical cospan modification"]
def mk
    (left : ψ.left ⟶ φ.left) (right : ψ.right ⟶ φ.right)
    (base : ψ.base ⟶ φ.base)
    (leftNaturality :
      left ▷ f' ≫ φ.leftIso.hom = ψ.leftIso.hom ≫ f ◁ base)
    (rightNaturality :
      right ▷ g' ≫ φ.rightIso.hom = ψ.rightIso.hom ≫ g ◁ base) :
    Pseudofunctor.StrongTrans.Hom ψ φ where
  as :=
    { app := Implementation.app left right base
      naturality :=
        Implementation.naturality left right base leftNaturality rightNaturality }

/- Data audit (mathlib 4.32): `mk` stores the three supplied component cells directly and
defers only the modification naturality field. No component `2`-morphism is selected by a
placeholder. -/

end CategoryTheory.Bicategory.CospanTransform.Hom
