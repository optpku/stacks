/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.StrictlyPerfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Restriction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Locally strictly perfect complexes on ringed spaces

The canonical owner is an `ObjectProperty` on cochain complexes of `𝒪_X`-modules.  Its
source-facing API exposes the witnessing open cover; comparisons with other presentations live
in separate bridge leaves.
-/

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

universe u

namespace AlgebraicGeometry.RingedSpace.CochainComplex

variable {X : RingedSpace.{u}}

/-- Example 20.50.2: complexes that become strictly perfect after restriction to every member
of one open cover of the ringed space. -/
@[stacks 0FP9 "object property"]
def locallyStrictlyPerfect :
    ObjectProperty (_root_.CochainComplex (Modules X) ℤ) :=
  fun E ↦ ∃ (ι : Type u) (U : ι → Opens X),
    IsOpenCover U ∧
      ∀ i : ι,
        _root_.SheafOfModules.CochainComplex.IsStrictlyPerfect
          (restrictedComplexOnOpen X (U i) E)

/-- Example 20.50.2: membership in the locally strictly perfect object property. -/
@[stacks 0FP9 "predicate"]
abbrev IsLocallyStrictlyPerfect
    (E : _root_.CochainComplex (Modules X) ℤ) : Prop :=
  locallyStrictlyPerfect E

/-- Locally strictly perfect complexes, as a full subcategory. -/
abbrev LocallyStrictlyPerfect :=
  (locallyStrictlyPerfect (X := X)).FullSubcategory

namespace LocallyStrictlyPerfect

/-- The canonical inclusion of locally strictly perfect complexes. -/
abbrev ι : LocallyStrictlyPerfect (X := X) ⥤
    _root_.CochainComplex (Modules X) ℤ :=
  ObjectProperty.ι _

end LocallyStrictlyPerfect

/-- Local strict perfectness unfolds to its explicit open-cover criterion. -/
theorem isLocallyStrictlyPerfect_iff_exists_openCover
    (E : _root_.CochainComplex (Modules X) ℤ) :
    IsLocallyStrictlyPerfect E ↔
      ∃ (ι : Type u) (U : ι → Opens X),
        IsOpenCover U ∧
          ∀ i : ι,
            _root_.SheafOfModules.CochainComplex.IsStrictlyPerfect
              (restrictedComplexOnOpen X (U i) E) := sorry

/-- An open cover by strictly perfect restrictions exhibits local strict perfectness. -/
theorem isLocallyStrictlyPerfect_of_isOpenCover
    {E : _root_.CochainComplex (Modules X) ℤ}
    {ι : Type u} {U : ι → Opens X}
    (hU : IsOpenCover U)
    (hE : ∀ i : ι,
      _root_.SheafOfModules.CochainComplex.IsStrictlyPerfect
        (restrictedComplexOnOpen X (U i) E)) :
    IsLocallyStrictlyPerfect E := sorry

/-- A locally strictly perfect complex admits a witnessing open cover. -/
theorem IsLocallyStrictlyPerfect.exists_openCover
    {E : _root_.CochainComplex (Modules X) ℤ}
    (hE : IsLocallyStrictlyPerfect E) :
    ∃ (ι : Type u) (U : ι → Opens X),
      IsOpenCover U ∧
        ∀ i : ι,
          _root_.SheafOfModules.CochainComplex.IsStrictlyPerfect
            (restrictedComplexOnOpen X (U i) E) := sorry

/-- Eliminate local strict perfectness through its witnessing open cover. -/
theorem IsLocallyStrictlyPerfect.elim
    {E : _root_.CochainComplex (Modules X) ℤ} {P : Prop}
    (hE : IsLocallyStrictlyPerfect E)
    (h : ∀ {ι : Type u} (U : ι → Opens X),
      IsOpenCover U →
        (∀ i : ι,
          _root_.SheafOfModules.CochainComplex.IsStrictlyPerfect
            (restrictedComplexOnOpen X (U i) E)) → P) :
    P := sorry

/-- Local strict perfectness is invariant under isomorphism of complexes. -/
instance locallyStrictlyPerfect_isClosedUnderIsomorphisms :
    (locallyStrictlyPerfect (X := X)).IsClosedUnderIsomorphisms := sorry

/-- Transport local strict perfectness along an isomorphism of complexes. -/
theorem IsLocallyStrictlyPerfect.of_iso
    {E F : _root_.CochainComplex (Modules X) ℤ}
    (hE : IsLocallyStrictlyPerfect E) (e : E ≅ F) :
    IsLocallyStrictlyPerfect F := sorry

end AlgebraicGeometry.RingedSpace.CochainComplex
