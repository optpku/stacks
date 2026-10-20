/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Sites.LeftExact

@[expose] public section
open CategoryTheory CategoryTheory.Limits
universe a b v w
namespace CategoryTheory.Functor.UniverseKan
variable {C : Type a} {D : Type b} [Category.{v} C] [Category.{w} D]

/-- Sheafification exists when values contain both object and morphism universes. -/
theorem sheafifyTypes (J : GrothendieckTopology C) :
    HasSheafify J (Type (max a v)) := by infer_instance

/-- A full comma limit exists when all index universes fit the value universe. -/
theorem typeRight (F : C ⥤ D) (P : Cᵒᵖ ⥤ Type (max a b v w)) :
    F.op.HasPointwiseRightKanExtension P := by
  intro V
  -- Local instance justification (defeq pin): this full comma index fits the displayed maximum universe.
  letI : HasLimitsOfShape (StructuredArrow V F.op) (Type (max a b v w)) := by infer_instance
  infer_instance

/-- The same bound supplies genuine left Kan extensions. -/
theorem typeLeft (F : C ⥤ D) (P : Cᵒᵖ ⥤ Type (max a b v w)) :
    F.op.HasLeftKanExtension P := by infer_instance

/-- Ring-valued comma limits exist at that actual coefficient universe. -/
theorem ringRight (F : C ⥤ D) (P : Cᵒᵖ ⥤ RingCat.{max a b v w}) :
    F.op.HasPointwiseRightKanExtension P := by
  intro V
  -- Local instance justification (defeq pin): ring-valued limits use that same full comma-index bound.
  letI : HasLimitsOfShape (StructuredArrow V F.op) RingCat.{max a b v w} := by infer_instance
  infer_instance

/-- Forgetting rings preserves these actual pointwise right Kan limits. -/
theorem forgetRight (F : C ⥤ D) :
    (forget RingCat.{max a b v w}).PreservesRightKanExtensions F.op := by
  intro P
  -- Local instance justification (proof-local temporary data): use the proved ring Kan certificate for this input P.
  letI : F.op.HasPointwiseRightKanExtension P := ringRight F P
  -- Local instance justification (proof-local temporary data): expose the actual cone proof at each comma object.
  letI (d : Dᵒᵖ) : PreservesLimit (StructuredArrow.proj d F.op ⋙ P)
      (forget RingCat.{max a b v w}) := by
    let Q := StructuredArrow.proj d F.op ⋙ P
    -- Local instance justification (defeq pin): the underlying type diagram has the same bounded comma index.
    letI : HasLimit (Q ⋙ forget RingCat.{max a b v w}) := by infer_instance
    -- Local instance justification (proof-local temporary data): derive this representation certificate from the actual limit.
    letI : Small.{max a b v w} (Q ⋙ forget RingCat.{max a b v w}).sections :=
      (Types.hasLimit_iff_small_sections _).mp inferInstance
    exact preservesLimit_of_preserves_limit_cone (RingCat.limitConeIsLimit Q)
      (Types.Small.limitConeIsLimit _)
  infer_instance

end CategoryTheory.Functor.UniverseKan
