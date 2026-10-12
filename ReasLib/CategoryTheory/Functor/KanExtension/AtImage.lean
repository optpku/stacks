/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pointwise Kan extensions at image objects

For a fully faithful functor, the identity costructured or structured arrow computes the
pointwise left or right Kan-extension diagram at an object in the image. This file records the
resulting canonical isomorphisms and their compatibility with Mathlib's explicit pointwise Kan
extensions.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {H : Type u₃} [Category.{v₃} H]

namespace LeftKanExtension.AtImage

variable (L : C ⥤ D) (F : C ⥤ H)

/-- At an object in the image of a fully faithful functor, the value of the original functor is
canonically isomorphic to the colimit computing the pointwise left Kan extension. -/
@[stacks 018M "pointwise left Kan extension at an image object"]
noncomputable def iso [L.Full] [L.Faithful] (X : C) :
    F.obj X ≅ colimit (CostructuredArrow.proj L (L.obj X) ⋙ F) :=
  @asIso H _ _ _
    (colimit.ι (CostructuredArrow.proj L (L.obj X) ⋙ F)
      (CostructuredArrow.mk (𝟙 (L.obj X))))
    (isIso_ι_of_isTerminal
      (CostructuredArrow.mkIdTerminal (S := L) (Y := X)) _)

/-- The forward map of the left-Kan-extension isomorphism at an image object is the colimit
injection indexed by the identity costructured arrow. -/
@[simp, stacks 018M "left Kan extension at an image object on the canonical injection"]
theorem iso_hom [L.Full] [L.Faithful] (X : C) :
    (iso L F X).hom =
      colimit.ι (CostructuredArrow.proj L (L.obj X) ⋙ F)
        (CostructuredArrow.mk (𝟙 (L.obj X))) := sorry

/-- Composing any colimit injection with the inverse of the image-object isomorphism applies
`F` to the unique preimage of the corresponding comma arrow. -/
@[reassoc (attr := simp), stacks 018M "left Kan extension at an image object on every leg"]
theorem ι_iso_inv [L.Full] [L.Faithful] (X : C)
    (g : CostructuredArrow L (L.obj X)) :
    colimit.ι (CostructuredArrow.proj L (L.obj X) ⋙ F) g ≫ (iso L F X).inv =
      F.map (L.preimage g.hom) := sorry

/-- The unit component of Mathlib's explicit pointwise left Kan extension is an isomorphism at
every object in the image of a fully faithful functor. -/
@[stacks 018M "pointwise left Kan extension unit at an image object"]
instance unit [L.Full] [L.Faithful]
    [L.HasPointwiseLeftKanExtension F] (X : C) :
    IsIso ((L.pointwiseLeftKanExtensionUnit F).app X) := sorry

/-- The canonical colimit isomorphism at an image object is the isomorphism induced by the
pointwise left-Kan-extension unit component. -/
@[stacks 018M "comparison with the pointwise left Kan extension unit"]
theorem iso_eq_unit [L.Full] [L.Faithful]
    [L.HasPointwiseLeftKanExtension F] (X : C) :
    iso L F X = asIso ((L.pointwiseLeftKanExtensionUnit F).app X) := sorry

end LeftKanExtension.AtImage

namespace RightKanExtension.AtImage

variable (L : C ⥤ D) (F : C ⥤ H)

/-- At an object in the image of a fully faithful functor, the limit computing the pointwise right
Kan extension is canonically isomorphic to the value of the original functor. -/
@[stacks 0184 "pointwise right Kan extension at an image object"]
noncomputable def iso [L.Full] [L.Faithful] (X : C) :
    limit (StructuredArrow.proj (L.obj X) L ⋙ F) ≅ F.obj X :=
  @asIso H _ _ _
    (limit.π (StructuredArrow.proj (L.obj X) L ⋙ F)
      (StructuredArrow.mk (𝟙 (L.obj X))))
    (isIso_π_of_isInitial
      (StructuredArrow.mkIdInitial (T := L) (Y := X)) _)

/-- The forward map of the right-Kan-extension isomorphism at an image object is the limit
projection indexed by the identity structured arrow. -/
@[simp, stacks 0184 "right Kan extension at an image object on the canonical projection"]
theorem iso_hom [L.Full] [L.Faithful] (X : C) :
    (iso L F X).hom =
      limit.π (StructuredArrow.proj (L.obj X) L ⋙ F)
        (StructuredArrow.mk (𝟙 (L.obj X))) := sorry

/-- Precomposing any limit projection with the inverse of the image-object isomorphism applies
`F` to the unique preimage of the corresponding comma arrow. -/
@[reassoc (attr := simp), stacks 0184 "right Kan extension at an image object on every leg"]
theorem iso_inv_π [L.Full] [L.Faithful] (X : C)
    (g : StructuredArrow (L.obj X) L) :
    (iso L F X).inv ≫ limit.π (StructuredArrow.proj (L.obj X) L ⋙ F) g =
      F.map (L.preimage g.hom) := sorry

/-- The counit component of Mathlib's explicit pointwise right Kan extension is an isomorphism at
every object in the image of a fully faithful functor. -/
@[stacks 0184 "pointwise right Kan extension counit at an image object"]
instance counit [L.Full] [L.Faithful]
    [L.HasPointwiseRightKanExtension F] (X : C) :
    IsIso ((L.pointwiseRightKanExtensionCounit F).app X) := sorry

/-- The canonical limit isomorphism at an image object is the isomorphism induced by the
pointwise right-Kan-extension counit component. -/
@[stacks 0184 "comparison with the pointwise right Kan extension counit"]
theorem iso_eq_counit [L.Full] [L.Faithful]
    [L.HasPointwiseRightKanExtension F] (X : C) :
    iso L F X = asIso ((L.pointwiseRightKanExtensionCounit F).app X) := sorry

end RightKanExtension.AtImage

end CategoryTheory.Functor
