module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Basic

/-!
# Right internal Homs in braided closed monoidal categories

This leaf transports mathlib's left-tensor internal-Hom adjunction across the
braiding, producing the right-oriented `RightInternalHom` owner used by the
project.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory Opposite

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace RightInternalHom

variable [BraidedCategory C]

section OfMonoidalClosed

variable [MonoidalClosed C]

section Implementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The pointwise braiding transport of `MonoidalClosed.internalHomAdjunction₂` is natural in
the internal-Hom parameter.

After expanding the transported Hom-equivalences, this is the parameter naturality of
`MonoidalClosed.internalHomAdjunction₂`, with the required interchange supplied by naturality of
the braiding. -/
private theorem ofBraidedClosed_homEquiv_naturality
    {X Y W Z : C} (f : X ⟶ Y) (g : W ⊗ Y ⟶ Z) :
    (((MonoidalClosed.internalHomAdjunction₂ (C := C)).adj X).ofNatIsoLeft
        (BraidedCategory.tensorLeftIsoTensorRight X)).homEquiv W Z (W ◁ f ≫ g) =
      (((MonoidalClosed.internalHomAdjunction₂ (C := C)).adj Y).ofNatIsoLeft
        (BraidedCategory.tensorLeftIsoTensorRight Y)).homEquiv W Z g ≫
        (MonoidalClosed.internalHom.map f.op).app Z := by
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply,
    Adjunction.homEquiv_ofNatIsoLeft_apply]
  change ((MonoidalClosed.internalHomAdjunction₂.adj X).homEquiv W Z)
      ((β_ X W).hom ≫ W ◁ f ≫ g) =
    ((MonoidalClosed.internalHomAdjunction₂.adj Y).homEquiv W Z)
      ((β_ Y W).hom ≫ g) ≫ (MonoidalClosed.internalHom.map f.op).app Z
  rw [← Category.assoc, ← BraidedCategory.braiding_naturality_left, Category.assoc]
  exact MonoidalClosed.internalHomAdjunction₂.homEquiv_naturality_one
    f ((β_ Y W).hom ≫ g)

/-- Assemble the transported pointwise adjunctions into a right internal-Hom owner. -/
private def ofBraidedClosed : RightInternalHom C where
  hom := MonoidalClosed.internalHom
  adj₂ := ParametrizedAdjunction.mk'
    (fun X =>
      ((MonoidalClosed.internalHomAdjunction₂ (C := C)).adj X).ofNatIsoLeft
        (BraidedCategory.tensorLeftIsoTensorRight X))
    (fun {X Y} f {W Z} g =>
      ofBraidedClosed_homEquiv_naturality (X := X) (Y := Y) (W := W) (Z := Z) f g)

end Implementation

/-- The canonical right-oriented internal-Hom structure in a braided monoidal closed category.

Its bifunctor is mathlib's `MonoidalClosed.internalHom`; at `X`, its adjunction
`(- ⊗ X) ⊣ internalHom(X, -)` is obtained from the standard
`(X ⊗ -) ⊣ internalHom(X, -)` by `BraidedCategory.tensorLeftIsoTensorRight X`. -/
@[stacks 0GWJ "braided closed right internal-Hom"]
def ofBraidedClosed : RightInternalHom C :=
  Implementation.ofBraidedClosed

/-- The representing bifunctor of `ofBraidedClosed` is mathlib's internal-Hom bifunctor. -/
@[simp, stacks 0GWJ "braided closed right internal-Hom bifunctor"]
theorem ofBraidedClosed.hom :
    (ofBraidedClosed (C := C)).hom = MonoidalClosed.internalHom := rfl

/-- Currying through `ofBraidedClosed` is ordinary monoidal-closed currying after braiding the
tensor factors into left-tensor order. -/
theorem ofBraidedClosed.curry {X W Y : C} (f : W ⊗ X ⟶ Y) :
    (ofBraidedClosed (C := C)).curry f = MonoidalClosed.curry ((β_ X W).hom ≫ f) := by
  change ((((MonoidalClosed.internalHomAdjunction₂ (C := C)).adj X).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight X)).homEquiv W Y) f = _
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  rfl

/-- Uncurrying through `ofBraidedClosed` is ordinary monoidal-closed uncurrying followed by the
inverse braiding into right-tensor order. -/
theorem ofBraidedClosed.uncurry {X W Y : C}
    (f : W ⟶ (X ⟶[ofBraidedClosed (C := C)]ᵣ Y)) :
    (ofBraidedClosed (C := C)).uncurry f =
      (β_ X W).inv ≫ MonoidalClosed.uncurry f := by
  change (((((MonoidalClosed.internalHomAdjunction₂ (C := C)).adj X).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight X)).homEquiv W Y).symm) f = _
  rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply]
  rfl

/-- Evaluation for `ofBraidedClosed` is the standard internal-Hom evaluation preceded by the
inverse braiding. -/
theorem ofBraidedClosed.ev (X Y : C) :
    (ofBraidedClosed (C := C)).ev X Y =
      (β_ X (X ⟶[C] Y)).inv ≫ (ihom.ev X).app Y := rfl

/-- Coevaluation for `ofBraidedClosed` is the standard internal-Hom coevaluation followed by the
action of the internal-Hom functor on the braiding. -/
theorem ofBraidedClosed.coev (X Y : C) :
    (ofBraidedClosed (C := C)).coev X Y =
      (ihom.coev X).app Y ≫ (ihom X).map (β_ X Y).hom := rfl

end Implementation

end OfMonoidalClosed

/-- The canonical right internal-Hom owner selected by an explicit monoidal-closed structure.
This bridge keeps the chosen structure as ordinary data and does not require a temporary instance. -/
@[stacks 0GWJ "explicit braided closed right internal-Hom"]
noncomputable abbrev ofBraidedClosedOf (H : MonoidalClosed C) : RightInternalHom C :=
  @ofBraidedClosed C _ _ _ H

/-- The pointwise adjunction of the explicit-owner bridge is the standard closed adjunction
transported from left tensoring to right tensoring by the braiding. -/
@[simp, stacks 0GWJ "explicit braided closed right internal-Hom adjunction"]
theorem ofBraidedClosedOf_adj (H : MonoidalClosed C) (X : C) :
    (ofBraidedClosedOf H).adj₂.adj X =
      ((@MonoidalClosed.internalHomAdjunction₂ C _ _ H).adj X).ofNatIsoLeft
        (BraidedCategory.tensorLeftIsoTensorRight X) := rfl

/-- The explicit-owner bridge has mathlib's internal-Hom bifunctor as its underlying functor. -/
@[simp, stacks 0GWJ "explicit braided closed right internal-Hom bifunctor"]
theorem ofBraidedClosedOf_hom (H : MonoidalClosed C) :
    (ofBraidedClosedOf H).hom = @MonoidalClosed.internalHom C _ _ H := rfl

/-- A chosen right internal-Hom structure induces a monoidal-closed structure after transporting
each right-tensor adjunction across the braiding.

This is a definition rather than a global instance: a category may already carry a distinct chosen
`MonoidalClosed` structure, and users should select this conversion locally when they need the
left-oriented mathlib API. -/
@[implicit_reducible, stacks 0GWJ "right internal-Hom to monoidal closed"]
def toMonoidalClosed (H : RightInternalHom C) : MonoidalClosed C where
  closed X :=
    { rightAdj := H.hom.obj (op X)
      adj := (H.adj₂.adj X).ofNatIsoLeft
        (BraidedCategory.tensorLeftIsoTensorRight X).symm }

end RightInternalHom

end CategoryTheory
