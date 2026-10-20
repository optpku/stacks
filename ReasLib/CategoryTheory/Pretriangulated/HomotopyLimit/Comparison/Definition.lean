module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparisons with Sequential Homotopy Limits

A `HomotopyLimit.Comparison` compares a cone over a sequential inverse system
with an explicit homotopy-limit presentation.  Naturality belongs to the source
cone, so downstream constructions do not need to carry a separate compatible
family of stage maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u v

namespace CategoryTheory.HomotopyLimit

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Stacks 08TC: a morphism from the point of a cone to a presented homotopy limit whose
composites with the presentation cone agree with the given cone. -/
@[stacks 08TC "comparison with a sequential homotopy limit"]
structure Comparison {K : SequentialInverseSystem D} (s : Cone K) {L : D}
    (c : s.pt ⟶ L) where
  /-- The explicit homotopy-limit presentation of the target. -/
  presentation : Presentation K L
  /-- The comparison morphism commutes with every leg of the two cones. -/
  comp_π (j : ℕᵒᵖ) :
    c ≫ presentation.cone.π.app j = s.π.app j

namespace Comparison

/-- Build comparison data from a morphism to the cone carried by an explicit target
presentation. -/
@[stacks 08TC]
def ofConeHom {K : SequentialInverseSystem D} {s : Cone K} {L : D}
    (P : Presentation K L) (f : s ⟶ P.cone) : Comparison s f.hom where
  presentation := P
  comp_π := f.w

/-- The target presentation stored by `ofConeHom` is the supplied presentation. -/
@[simp]
theorem ofConeHom_presentation {K : SequentialInverseSystem D} {s : Cone K} {L : D}
    (P : Presentation K L) (f : s ⟶ P.cone) :
    (ofConeHom P f).presentation = P := sorry

/-- Pointwise compatibility with the stage projections supplies the cone compatibility used by
`ofPresentation`. -/
theorem ofPresentation_comp_π {K : SequentialInverseSystem D} {s : Cone K} {L : D}
    {c : s.pt ⟶ L} (P : Presentation K L)
    (h : ∀ n : ℕ, c ≫ P.stageProjection n = s.π.app (op n)) (j : ℕᵒᵖ) :
    c ≫ P.cone.π.app j = s.π.app j := sorry

/-- Build comparison data from an explicit target presentation and pointwise stage equations.
This is the bridge for source data initially presented as components rather than a cone
morphism. -/
@[stacks 08TC]
def ofPresentation {K : SequentialInverseSystem D} {s : Cone K} {L : D}
    {c : s.pt ⟶ L} (P : Presentation K L)
    (h : ∀ n : ℕ, c ≫ P.stageProjection n = s.π.app (op n)) :
    Comparison s c where
  presentation := P
  comp_π := ofPresentation_comp_π P h

/-- The target presentation stored by `ofPresentation` is the supplied presentation. -/
@[simp]
theorem ofPresentation_presentation {K : SequentialInverseSystem D} {s : Cone K} {L : D}
    {c : s.pt ⟶ L} (P : Presentation K L)
    (h : ∀ n : ℕ, c ≫ P.stageProjection n = s.π.app (op n)) :
    (ofPresentation P h).presentation = P := sorry

/-- A comparison is canonically a morphism from its source cone to the cone carried by its
target presentation. -/
@[stacks 08TC]
def coneHom {K : SequentialInverseSystem D} {s : Cone K} {L : D}
    {c : s.pt ⟶ L} (C : Comparison s c) : s ⟶ C.presentation.cone where
  hom := c
  w := C.comp_π

/-- The map on cone points of the cone morphism underlying a comparison is the comparison
morphism. -/
@[simp]
theorem coneHom_hom {K : SequentialInverseSystem D} {s : Cone K} {L : D}
    {c : s.pt ⟶ L} (C : Comparison s c) : C.coneHom.hom = c := sorry

/-- The comparison morphism followed by a presentation stage projection is the corresponding
leg of the source cone. -/
@[reassoc, stacks 08TC]
theorem comp_stageProjection {K : SequentialInverseSystem D} {s : Cone K} {L : D}
    {c : s.pt ⟶ L} (C : Comparison s c) (n : ℕ) :
    c ≫ C.presentation.stageProjection n = s.π.app (op n) := sorry

/-- The identity of a presented homotopy limit compares its presentation cone with the
presentation itself. -/
@[stacks 08TC]
def id {K : SequentialInverseSystem D} {L : D} (P : Presentation K L) :
    Comparison P.cone (𝟙 L) :=
  ofConeHom P (𝟙 P.cone)

/-- The target presentation stored by the identity comparison is the original presentation. -/
@[simp]
theorem id_presentation {K : SequentialInverseSystem D} {L : D}
    (P : Presentation K L) : (id P).presentation = P := sorry

/-- Precompose a comparison by a morphism to the point of its source cone. -/
@[stacks 08TC]
def precomp {K : SequentialInverseSystem D} {s : Cone K} {L W : D}
    {c : s.pt ⟶ L} (C : Comparison s c) (e : W ⟶ s.pt) :
    Comparison (s.extend e) (e ≫ c) :=
  ofConeHom C.presentation (s.extendHom e ≫ C.coneHom)

/-- Precomposition retains the target presentation. -/
@[simp]
theorem precomp_presentation {K : SequentialInverseSystem D} {s : Cone K} {L W : D}
    {c : s.pt ⟶ L} (C : Comparison s c) (e : W ⟶ s.pt) :
    (C.precomp e).presentation = C.presentation := sorry

/-- The target of comparison data satisfies the intrinsic homotopy-limit predicate. -/
@[stacks 08TC]
theorem isOf {K : SequentialInverseSystem D} {s : Cone K} {L : D}
    {c : s.pt ⟶ L} (C : Comparison s c) : HomotopyLimit.IsOf K L := sorry

end Comparison

end CategoryTheory.HomotopyLimit
