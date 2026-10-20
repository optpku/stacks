/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.FieldTheory.Transcendence.PurelyTranscendental
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme

/-!
# Scheme representability after purely transcendental field extension

A quasi-separated algebraic space over a field is a scheme if it becomes a
scheme after base change along a purely transcendental field extension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsScheme

/-- If the base change of a quasi-separated algebraic space along a purely
transcendental field extension is a scheme, then the original algebraic space
is a scheme. -/
theorem of_isScheme_baseChange_isPurelyTranscendental {k K : Type u} [Field k] [Field K]
    [Algebra k K] (hK : _root_.FieldExtension.IsPurelyTranscendental k K)
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) [IsAbsolutelyQuasiSeparated X]
    (hX : IsScheme (baseChange (FieldExtension.specMap k K) X)) :
    IsScheme X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsScheme
