/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme

/-!
# Scheme representability after field extension

A quasi-separated algebraic space over a field that becomes a scheme after some
field-extension base change becomes a scheme over the algebraic closure. If it
is also quasi-compact, it becomes a scheme over a finite separable extension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsScheme

/-- If the base change of a quasi-separated algebraic space along a field extension
is a scheme, then the base change along the algebraic closure is a scheme. -/
theorem of_baseChange_algebraicClosure {k K : Type u} [Field k] [Field K]
    [Algebra k K] (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    [IsAbsolutelyQuasiSeparated X]
    (hX : IsScheme (baseChange (FieldExtension.specMap k K) X)) :
    IsScheme (baseChange (FieldExtension.specMap k (AlgebraicClosure k)) X) :=
  sorry

/-- If a quasi-compact quasi-separated algebraic space becomes a scheme after base
change along a field extension, then it becomes a scheme after base change along
some finite separable extension. -/
theorem exists_finiteSeparable_of_baseChange {k K : Type u} [Field k] [Field K]
    [Algebra k K] (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    [IsAbsolutelyQuasiSeparated X] [IsQuasiCompact X]
    (hX : IsScheme (baseChange (FieldExtension.specMap k K) X)) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k') (_ : Algebra.IsSeparable k k'),
      IsScheme (baseChange (FieldExtension.specMap k k') X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsScheme
