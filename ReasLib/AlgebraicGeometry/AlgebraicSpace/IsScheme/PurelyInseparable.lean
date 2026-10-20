/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme

/-!
# Scheme representability and purely inseparable extensions

An algebraic space over a field is a scheme if it becomes a scheme after
base change to a purely inseparable field extension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsScheme

/-- If the base change of an algebraic space along a purely inseparable field
extension is a scheme, then the original algebraic space is a scheme. -/
theorem of_isScheme_baseChange_isPurelyInseparable {k k' : Type u} [Field k] [Field k']
    [Algebra k k'] [IsPurelyInseparable k k']
    (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    (hX : IsScheme (baseChange (FieldExtension.specMap k k') X)) :
    IsScheme X :=
  sorry

/-- An algebraic space over a field is a scheme if there exists a purely
inseparable field extension over which its base change is a scheme. -/
theorem of_baseChange_isPurelyInseparable {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    (hX : ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : IsPurelyInseparable k k'),
      IsScheme (baseChange (FieldExtension.specMap k k') X)) :
    IsScheme X := by
  obtain ⟨k', fieldK, algebraK, purelyInseparableK, hX⟩ := hX
  exact @of_isScheme_baseChange_isPurelyInseparable k k' inferInstance fieldK
    algebraK purelyInseparableK X hX

end AlgebraicGeometry.AlgebraicSpace.IsScheme
