/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.DerivedFunctor.Grothendieck
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.KInjective.Global
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure

@[expose] public section

/-!
# Triangulated Sequential Derived Limit

Source-definedness everywhere gives the canonical sequential derived-limit functor its
total-derived shift comparison and triangulated exactness (Stacks 05SE). Grothendieck
abelian categories supply source-definedness through K-injective resolutions.

The separate preservation result of Stacks 08U1, including its countable-product hypotheses,
is `Functor.RightDerived.KInjective.preservesHomotopyLimit` in `Limit.Preservation`.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe w wA wSys u v

namespace CategoryTheory.DerivedLimit

variable (A : Type u) [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasLimitsOfShape ℕᵒᵖ A]
variable [(lim : SequentialInverseSystem A ⥤ A).Additive]

/-- The source-definedness condition for total right derived sequential inverse limit.
This condition concerns the localization-indexed diagrams, rather than shift or exactness data. -/
abbrev HasEverywhereDefinedDerivedFunctor : Prop :=
  Functor.RightDerived.EverywhereDefined
    (Functor.Homotopy.toDerived (lim : SequentialInverseSystem A ⥤ A))
    (HomotopyCategory.quasiIso (SequentialInverseSystem A) (up ℤ))

/-- Compatibility name for the everywhere-definedness construction assumption.
It stores no selected shift comparison and no triangulated-exactness conclusion. -/
abbrev TriangulatedModel : Prop := HasEverywhereDefinedDerivedFunctor A

namespace TriangulatedModel

/-- Retain the compatibility constructor using source-definedness as its input. -/
theorem of [h : HasEverywhereDefinedDerivedFunctor A] : TriangulatedModel A := h

end TriangulatedModel

/-- K-injective resolutions of sequential systems give source-definedness everywhere.
The resolutions use the existing functorial Grothendieck construction. -/
theorem HasEverywhereDefinedDerivedFunctor.ofGrothendieck
    [IsGrothendieckAbelian.{w} A] : HasEverywhereDefinedDerivedFunctor A := by
  apply Functor.KInjective.RightDerived.EverywhereDefined.of_kInjective_resolutions
  intro K
  exact ⟨CochainComplex.KInjectiveResolution.mk
    ((CochainComplex.KInjectiveResolution.Construction.replacement.{w}
      (SequentialInverseSystem A)).obj K)
    (CochainComplex.KInjectiveResolution.Construction.replacement_isKInjective
      (SequentialInverseSystem A) K)
    ((CochainComplex.KInjectiveResolution.Construction.augmentation.{w}
      (SequentialInverseSystem A)).app K)
    (CochainComplex.KInjectiveResolution.Construction.augmentation_quasiIso
      (SequentialInverseSystem A) K)⟩

variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]
variable [HasDerivedFunctor A]

/-- The shift comparison is the canonical one on the total right derived functor. -/
@[stacks 05SE "sequential derived-limit shift comparison"]
noncomputable instance functor.commShift [HasEverywhereDefinedDerivedFunctor A] :
    (functor A).CommShift ℤ :=
  Functor.totalRightDerived_commShift
    (Functor.Homotopy.toDerived (lim : SequentialInverseSystem A ⥤ A))
    (HomotopyCategory.quasiIso (SequentialInverseSystem A) (up ℤ))
    (DerivedCategory.Qh (C := SequentialInverseSystem A))

/-- The sequential derived-limit comparison is anchored to the total-derived comparison. -/
@[simp]
theorem functor.commShiftIso_eq_totalRightDerivedShiftIso
    [HasEverywhereDefinedDerivedFunctor A] (n : ℤ) :
    (functor A).commShiftIso n =
      Functor.totalRightDerivedShiftIso
        (Functor.Homotopy.toDerived (lim : SequentialInverseSystem A ⥤ A))
        (HomotopyCategory.quasiIso (SequentialInverseSystem A) (up ℤ))
        (DerivedCategory.Qh (C := SequentialInverseSystem A)) n := rfl

/-- An everywhere source-defined sequential derived-limit functor is triangulated,
with respect to its canonical total-derived shift comparison. -/
@[stacks 05SE "sequential derived-limit exactness"]
instance functor.isTriangulated [HasEverywhereDefinedDerivedFunctor A] :
    (functor A).IsTriangulated :=
  Functor.totalRightDerived_isTriangulated
    (Functor.Homotopy.toDerived (lim : SequentialInverseSystem A ⥤ A))
    (HomotopyCategory.quasiIso (SequentialInverseSystem A) (up ℤ))
    (DerivedCategory.Qh (C := SequentialInverseSystem A))

/-- The canonical shift comparison under the former projection name. -/
noncomputable abbrev TriangulatedModel.commShift [TriangulatedModel A] :
    (functor A).CommShift ℤ := functor.commShift A

/-- The derived exactness theorem under the former projection name. -/
theorem TriangulatedModel.isTriangulated [TriangulatedModel A] :
    (functor A).IsTriangulatedWith (TriangulatedModel.commShift A) :=
  functor.isTriangulated A

/-- Source-definedness yields the construction-neutral Prop-valued exactness interface. -/
theorem TriangulatedModel.hasTriangulatedStructure [TriangulatedModel A] :
    (functor A).HasTriangulatedStructure :=
  ⟨functor.commShift A, functor.isTriangulated A⟩

/-- The standard Grothendieck situation supplies the exact sequential derived-limit functor.
Countable-product exactness is needed for preservation of homotopy limits, separately from
this triangulated-exactness conclusion. -/
@[stacks 05SE "Grothendieck sequential derived-limit exactness"]
theorem functor.hasTriangulatedStructure_ofGrothendieck
    [IsGrothendieckAbelian.{w} A] : (functor A).HasTriangulatedStructure := by
  letI := HasEverywhereDefinedDerivedFunctor.ofGrothendieck A
  exact TriangulatedModel.hasTriangulatedStructure A

end CategoryTheory.DerivedLimit
