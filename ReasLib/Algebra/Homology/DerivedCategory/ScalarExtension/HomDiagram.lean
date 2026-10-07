module

public import ReasLib.CategoryTheory.DerivedCategory.FilteredColimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Concrete filtered Hom diagrams

This leaf owns the data layer for a filtered Hom computation.  A caller gives
the actual stage functor, target type, and stage-to-target maps; the generic
filtered-colimit consequences remain in `DerivedCategory.FilteredColimit`.
No ring, tensor, or derived-category choice is hidden here, so the same owner
can be instantiated by module, sheaf, or triangulated Hom systems.

@stack 0DHX
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.DerivedCategory.FilteredColimit

variable {I : Type v} [Category.{w} I]

/-- A category-colimit certificate is independent of any derived or ring model. -/
@[stacks 0DHX "category-colimit certificate for a stage diagram"]
structure CategoryColimit (C : I ⥤ Cat.{u}) where
  /-- The category-valued cocone. -/
  cocone : Cocone C
  /-- The universal property of the cocone. -/
  isColimit : IsColimit cocone

namespace CategoryColimit

/-- The canonical certificate when the category-valued colimit is available. -/
@[stacks 0DHX "canonical category-colimit certificate"]
noncomputable def ofHasColimit (C : I ⥤ Cat.{u}) [HasColimit C] : CategoryColimit C :=
  { cocone := colimit.cocone C
    isColimit := colimit.isColimit C }

end CategoryColimit

/-- `0DHX`: explicit stage maps into a target for a filtered Hom diagram. -/
@[stacks 0DHX "concrete filtered Hom diagram data"]
structure HomDiagram (F : I ⥤ Type u) (T : Type u) where
  /-- The map from each stage into the target. -/
  ι : ∀ i, F.obj i → T
  /-- Compatibility of the stage maps with every transition morphism. -/
  natural : ∀ ⦃i j⦄ (f : i ⟶ j) (x : F.obj i),
    ι j (F.map f x) = ι i x

namespace HomDiagram

variable {F : I ⥤ Type u} {T : Type u} (D : HomDiagram F T)

/-- The explicit cocone determined by the stage maps. -/
@[stacks 0DHX "concrete filtered Hom cocone"]
noncomputable abbrev cocone : Cocone F :=
  mkCocone F _ D.ι D.natural

/-- Add the colimit certificate to obtain the shared filtered Hom comparison owner. -/
@[stacks 0DHX "concrete filtered Hom comparison"]
noncomputable def comparison (h : IsColimit D.cocone) : HomComparison F T :=
  { ι := D.ι
    natural := D.natural
    isColimit := h }

section

variable [IsFilteredOrEmpty I]

/-- Every target element is represented by one explicit stage map. -/
@[stacks 0DHX "concrete filtered Hom factorization"]
theorem factor (h : IsColimit D.cocone) (x : T) :
    ∃ (i : I) (y : F.obj i), x = D.ι i y := sorry

/-- Equality of two stage representatives is eventually witnessed in the diagram. -/
@[stacks 0DHX "concrete filtered Hom eventual equality"]
theorem eventually_eq (h : IsColimit D.cocone) {i : I}
    (x y : F.obj i) (hxy : D.ι i x = D.ι i y) :
    ∃ (j : I) (f : i ⟶ j), F.map f x = F.map f y := sorry

/-- A property-preserving filtered representation of a target element. -/
@[stacks 0DHX "filtered descent of a designated property"]
theorem exists_stage_of_property
    (h : IsColimit D.cocone)
    (Pstage : ∀ i, F.obj i → Prop) (Ptarget : T → Prop)
    (hmap : ∀ (i : I) (y : F.obj i), Ptarget (D.ι i y) → Pstage i y)
    {x : T} (hx : Ptarget x) :
    ∃ (i : I) (y : F.obj i), Pstage i y ∧ x = D.ι i y := sorry

end

end HomDiagram

end CategoryTheory.DerivedCategory.FilteredColimit
