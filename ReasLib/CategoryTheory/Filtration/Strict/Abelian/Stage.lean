/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Strict.Abelian.Basic

/-!
# Consecutive Stages of Abelian Filtered Objects

This file provides the canonical short exact row for consecutive filtration stages and the
stagewise isomorphism criteria used in finite-filtration arguments.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FilteredObject.Hom

open FilteredObject

variable [Abelian C]
variable {A B : FilteredObject C}

/-- The canonical short complex from the `(p + 1)`-st filtration stage through the `p`-th stage
to the `p`-th graded piece. -/
abbrev stageShortComplex (X : FilteredObject C) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (X.filtration.succInclusion p)
    (cokernel.π (X.filtration.succInclusion p))
    (cokernel.condition (X.filtration.succInclusion p))

/-- Consecutive filtration stages and the corresponding graded piece form a short exact row. -/
theorem stage_shortExact (X : FilteredObject C) (p : ℤ) :
    (stageShortComplex X p).ShortExact := sorry

namespace StageMap

/-- A monic filtered morphism induces monic maps on every filtration stage. -/
theorem mono_of_hom_mono (g : A ⟶ B) [Mono g.hom] (p : ℤ) :
    Mono (stageMap g p) := sorry

/-- The right square of the canonical stage-row map commutes. -/
theorem toShortComplex_right_comm (g : A ⟶ B) (p : ℤ) :
    stageMap g p ≫ cokernel.π (B.filtration.succInclusion p) =
      cokernel.π (A.filtration.succInclusion p) ≫ gradedPieceMap g p := sorry

/-- A filtered morphism induces a morphism between its canonical stage rows. -/
def toShortComplex (g : A ⟶ B) (p : ℤ) :
    FilteredObject.Hom.stageShortComplex A p ⟶ FilteredObject.Hom.stageShortComplex B p :=
  ShortComplex.homMk (stageMap g (p + 1)) (stageMap g p) (gradedPieceMap g p)
    (succInclusion_naturality g p).symm (toShortComplex_right_comm g p)

end StageMap

/-- Once a decreasing filtration is zero at one stage, all later stages are zero. -/
theorem filtration_eq_bot_of_le {X : FilteredObject C} {p q : ℤ}
    (hpq : p ≤ q) (hp : X.filtration p = ⊥) : X.filtration q = ⊥ := sorry

/-- Once a decreasing filtration is the whole object at one stage, all earlier stages are the
whole object. -/
theorem filtration_eq_top_of_le {X : FilteredObject C} {p q : ℤ}
    (hpq : p ≤ q) (hq : X.filtration q = ⊤) : X.filtration p = ⊤ := sorry

/-- A zero filtration stage is the canonical zero subobject. -/
theorem stage_eq_mk_zero_of_eq_bot (X : FilteredObject C) (p : ℤ)
    (hp : X.filtration p = ⊥) :
    X.filtration.stage p = Subobject.mk (0 : (0 : C) ⟶ X.obj) := sorry

namespace Stage

/-- A filtration stage equal to the bottom subobject is canonically isomorphic to zero. -/
noncomputable def isoZero_of_eq_bot (X : FilteredObject C) (p : ℤ)
    (hp : X.filtration p = ⊥) : X.stage p ≅ 0 :=
  Subobject.isoOfEqMk (X.filtration.stage p) (0 : (0 : C) ⟶ X.obj)
    (stage_eq_mk_zero_of_eq_bot X p hp)

end Stage

/-- A filtration stage equal to the bottom subobject is a zero object. -/
theorem stage_isZero_of_eq_bot (X : FilteredObject C) (p : ℤ)
    (hp : X.filtration p = ⊥) : IsZero (X.stage p) := sorry

namespace StageMap

namespace IsIso

/-- A stage map between two zero filtration stages is an isomorphism. -/
theorem of_eq_bot (g : A ⟶ B) (p : ℤ)
    (hA : A.filtration p = ⊥) (hB : B.filtration p = ⊥) :
    IsIso (stageMap g p) := sorry

/-- If both stages are whole and the ambient map is an isomorphism, the stage map is an
isomorphism. -/
theorem of_eq_top (g : A ⟶ B) (p : ℤ)
    (hA : A.filtration p = ⊤) (hB : B.filtration p = ⊤) [IsIso g.hom] :
    IsIso (stageMap g p) := sorry

end IsIso

namespace GradedPiece

/-- An isomorphism of associated graded objects is an isomorphism on every graded piece. -/
theorem isIso_of_associatedGraded (g : A ⟶ B)
    [IsIso (associatedGradedMap g)] (p : ℤ) : IsIso (gradedPieceMap g p) := sorry

/-- Explicit-hypothesis form of degreewise evaluation of an associated-graded isomorphism. -/
theorem isIso_of (g : A ⟶ B)
    (hg : IsIso (associatedGradedMap g)) (p : ℤ) : IsIso (gradedPieceMap g p) := sorry

end GradedPiece

namespace IsIso

/-- In canonical stage rows, isomorphisms on the successor stage and graded piece imply an
isomorphism on the current stage. -/
theorem of_succ_of_gradedPiece (g : A ⟶ B) (p : ℤ)
    [IsIso (stageMap g (p + 1))] [IsIso (gradedPieceMap g p)] :
    IsIso (stageMap g p) := sorry

/-- In canonical stage rows, an isomorphism on the current stage and a monomorphism on the
graded piece imply an isomorphism on the successor stage. -/
theorem succ_of_gradedPiece_mono (g : A ⟶ B) (p : ℤ)
    [IsIso (stageMap g p)] [Mono (gradedPieceMap g p)] :
    IsIso (stageMap g (p + 1)) := sorry

/-- In canonical stage rows, an isomorphism on the successor stage and an epimorphism on the
graded piece imply an isomorphism on the current stage. -/
theorem of_succ_of_gradedPiece_epi (g : A ⟶ B) (p : ℤ)
    [Mono g.hom] [IsIso (stageMap g (p + 1))] [Epi (gradedPieceMap g p)] :
    IsIso (stageMap g p) := sorry

/-- A common zero stage, an ambient isomorphism, and an associated-graded isomorphism imply
stagewise isomorphisms. -/
theorem of_hom_of_associatedGraded (g : A ⟶ B)
    (m : ℤ) (hA : A.filtration m = ⊥) (hB : B.filtration m = ⊥)
    [IsIso g.hom] [IsIso (associatedGradedMap g)] (p : ℤ) :
    IsIso (stageMap g p) := sorry

/-- A common zero stage and isomorphisms on all graded pieces imply isomorphisms on all
filtration stages. -/
theorem of_eq_bot_of_all_gradedPiece (g : A ⟶ B)
    (m : ℤ) (hA : A.filtration m = ⊥) (hB : B.filtration m = ⊥)
    (hgraded : ∀ p : ℤ, IsIso (gradedPieceMap g p)) (p : ℤ) :
    IsIso (stageMap g p) := sorry

/-- An ambient isomorphism whose maps on all filtration stages are isomorphisms is an isomorphism
of filtered objects. -/
theorem of_hom_of_all (g : A ⟶ B) [IsIso g.hom]
    (hstage : ∀ p : ℤ, IsIso (stageMap g p)) : IsIso g := sorry

end IsIso
end StageMap

end FilteredObject.Hom

end CategoryTheory
