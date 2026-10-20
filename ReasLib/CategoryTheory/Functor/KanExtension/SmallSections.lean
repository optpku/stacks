module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Right Kan extensions with small compatible sections

A large comma category can index a limit in `Type w` when the type of
compatible sections is `w`-small. The native type and ring limit cones use
these actual sections; the size of the whole comma category need not shrink.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe uC vC uD vD w

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- Native compatible-section limits give a pointwise right Kan extension.
The hypothesis concerns the displayed diagram, not all presheaves. -/
instance hasPointwiseRightKanExtension_of_small_sections
    (L : C ⥤ D) (P : C ⥤ Type w)
    [∀ Y : D, Small.{w} (StructuredArrow.proj Y L ⋙ P).sections] :
    L.HasPointwiseRightKanExtension P :=
  fun Y ↦ HasLimit.mk
    ⟨Types.Small.limitCone (StructuredArrow.proj Y L ⋙ P),
      Types.Small.limitConeIsLimit (StructuredArrow.proj Y L ⋙ P)⟩

/-- The ring limit uses the subring of actual compatible sections of its underlying diagram. -/
instance hasPointwiseRightKanExtension_ring_of_small_sections
    (L : C ⥤ D) (P : C ⥤ RingCat.{w})
    [∀ Y : D, Small.{w} ((StructuredArrow.proj Y L ⋙ P) ⋙ forget RingCat.{w}).sections] :
    L.HasPointwiseRightKanExtension P :=
  fun Y ↦ HasLimit.mk
    ⟨RingCat.limitCone (StructuredArrow.proj Y L ⋙ P),
      RingCat.limitConeIsLimit (StructuredArrow.proj Y L ⋙ P)⟩

/-- Forgetting rings preserves the actual compatible-section cone, including at large indices. -/
instance preservesLimit_forget_ring_of_small_sections
    {J : Type uC} [Category.{vC} J] (P : J ⥤ RingCat.{w})
    [Small.{w} (P ⋙ forget RingCat.{w}).sections] :
    PreservesLimit P (forget RingCat.{w}) :=
  preservesLimit_of_preserves_limit_cone (RingCat.limitConeIsLimit P)
    (Types.Small.limitConeIsLimit (P ⋙ forget RingCat.{w}))

/-- The ring forgetful functor preserves the right Kan extension of a particular
diagram with small compatible sections. -/
instance preservesRightKanExtension_forget_ring_of_small_sections
    (L : C ⥤ D) (P : C ⥤ RingCat.{w})
    [∀ Y : D, Small.{w} ((StructuredArrow.proj Y L ⋙ P) ⋙ forget RingCat.{w}).sections] :
    (forget RingCat.{w}).PreservesRightKanExtension P L :=
  letI : (forget RingCat.{w}).PreservesPointwiseRightKanExtension P L :=
    fun Y ↦ preservesPointwiseRightKanExtensionAtOfPreservesLimit
      (forget RingCat.{w}) P L Y
  preservesPointwiseRKEOfHasPointwiseAndPreservesPointwise
    (forget RingCat.{w}) P L

end CategoryTheory.Functor
