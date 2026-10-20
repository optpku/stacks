/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.DerivedFunctor
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure

@[expose] public section

/-!
# Triangulated Models of Sequential Derived Limit

This optional leaf packages shift comparison and triangulated exactness for
the canonical sequential derived-limit functor.
-/

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe wA wSys u v

namespace CategoryTheory.DerivedLimit

variable (A : Type u) [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasLimitsOfShape ℕᵒᵖ A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]
variable [(lim : SequentialInverseSystem A ⥤ A).Additive]
variable [HasDerivedFunctor A]

/-- A concrete model in which sequential derived inverse limit carries shift
comparison and triangulated exactness data. -/
@[stacks 08U1 "sequential derived-limit triangulated model"]
class TriangulatedModel where
  /-- The canonical derived inverse-limit functor commutes with cohomological shifts. -/
  commShift : (functor A).CommShift ℤ
  /-- The canonical derived inverse-limit functor preserves distinguished triangles. -/
  isTriangulated : (functor A).IsTriangulatedWith commShift

namespace TriangulatedModel

/-- Bundle existing shift and triangulated instances into a sequential
derived-limit model. This is deliberately not an instance. -/
@[stacks 08U1 "assemble a sequential derived-limit triangulated model", reducible]
noncomputable def of
    [commShift : (functor A).CommShift ℤ]
    [isTriangulated : (functor A).IsTriangulated] :
    TriangulatedModel A where
  commShift := commShift
  isTriangulated := isTriangulated

end TriangulatedModel

/-- A selected triangulated model yields the construction-neutral
Prop-valued exactness interface. -/
theorem TriangulatedModel.hasTriangulatedStructure [TriangulatedModel A] :
    (functor A).HasTriangulatedStructure := sorry

/-- The shift comparison supplied by a sequential derived-limit model is used automatically. -/
instance functor.commShift [TriangulatedModel A] :
    (functor A).CommShift ℤ :=
  TriangulatedModel.commShift

/-- The triangulated exactness supplied by a sequential derived-limit model is used automatically. -/
instance functor.isTriangulated [TriangulatedModel A] :
    (functor A).IsTriangulated :=
  TriangulatedModel.isTriangulated

end CategoryTheory.DerivedLimit
