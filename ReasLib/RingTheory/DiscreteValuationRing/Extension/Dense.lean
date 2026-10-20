/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic
public import ReasLib.RingTheory.Completion.LocalRing
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# Extension-dense classes of discrete valuation rings
-/

@[expose]
public section

universe u

/-- A class of discrete valuation rings is extension-dense if every discrete
valuation ring admits an extension belonging to the class. -/
class IsDiscreteValuationRing.ExtensionDense
    (P : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R], Prop) :
    Prop where
  /-- Every discrete valuation ring admits an extension in the class `P`. -/
  exists_extension :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R],
      ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
        (_ : Algebra R R'),
        IsExtensionOfDiscreteValuationRings R R' ∧ P R'

namespace IsDiscreteValuationRing.ExtensionDense

/-- Complete discrete valuation rings form an extension-dense class: every
discrete valuation ring admits a complete discrete valuation ring extension. -/
instance completeLocalRing :
    ExtensionDense fun (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] ↦
      IsCompleteLocalRing R :=
  sorry

/-- A predicate on discrete valuation rings is extension-dense if and only if
every discrete valuation ring admits an extension in the class. -/
theorem spec
    (P : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R], Prop) :
    ExtensionDense P ↔
      ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R],
        ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
          (_ : Algebra R R'),
          IsExtensionOfDiscreteValuationRings R R' ∧ P R' :=
  sorry

end IsDiscreteValuationRing.ExtensionDense

namespace IsDiscreteValuationRing.ExtensionDense

/-- Complete
discrete valuation rings with algebraically closed residue field form an
extension-dense class of discrete valuation rings. -/
instance completeAlgClosedResidue :
    ExtensionDense fun (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] ↦
      IsCompleteLocalRing R ∧ IsAlgClosed (IsLocalRing.ResidueField R) :=
  sorry

end IsDiscreteValuationRing.ExtensionDense

