/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Irreducible

/-!
# Minimal nonscheme algebraic spaces

An algebraic space is a minimal nonscheme when it is not a scheme, but every
closed subspace whose inclusion is not an isomorphism is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is a minimal nonscheme if it is not a scheme, while every
closed subspace whose inclusion is not an isomorphism is a scheme. -/
def IsMinimalNonscheme {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop :=
  ¬ IsScheme X ∧ ∀ Z : ClosedSubspace X, ¬ IsIso Z.ι → IsScheme Z.X

/-- `IsMinimalNonscheme X` means that `X` is not a scheme, while every closed
subspace of `X` whose inclusion is not an isomorphism is a scheme. -/
theorem isMinimalNonscheme_iff {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsMinimalNonscheme X ↔
      ¬ IsScheme X ∧ ∀ Z : ClosedSubspace X, ¬ IsIso Z.ι → IsScheme Z.X :=
  sorry

/-- A minimal nonscheme algebraic space is not a scheme. -/
theorem not_isScheme_of_isMinimalNonscheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    (hX : IsMinimalNonscheme X) : ¬ IsScheme X :=
  sorry

/-- Every closed subspace of a minimal nonscheme whose inclusion is not an
isomorphism is a scheme. -/
theorem isScheme_of_isMinimalNonscheme_of_not_isIso {S : Scheme.{u}}
    {X : AlgebraicSpace S} (hX : IsMinimalNonscheme X) (Z : ClosedSubspace X)
    (hZ : ¬ IsIso Z.ι) : IsScheme Z.X :=
  sorry

/-- Every quasi-compact, absolutely quasi-separated algebraic space that is not
a scheme contains a closed subspace that is a minimal nonscheme. -/
theorem exists_closedSubspace_isMinimalNonscheme {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (hX : ¬ IsScheme X) :
    ∃ Z : ClosedSubspace X, IsMinimalNonscheme Z.X :=
  sorry

/-- A quasi-compact, absolutely quasi-separated minimal nonscheme algebraic space
is reduced. -/
theorem IsReduced.of_isMinimalNonscheme {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (hX : IsMinimalNonscheme X) : IsReduced X :=
  sorry

/-- A quasi-compact, absolutely quasi-separated minimal nonscheme algebraic space
is irreducible. -/
theorem IsIrreducible.of_isMinimalNonscheme {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (hX : IsMinimalNonscheme X) : IsIrreducible X :=
  sorry

/-- A quasi-compact, absolutely quasi-separated algebraic space known to be a
minimal nonscheme is reduced. -/
instance instIsReducedOfIsMinimalNonscheme {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] [Fact (IsMinimalNonscheme X)] :
    IsReduced X :=
  IsReduced.of_isMinimalNonscheme X Fact.out

/-- A quasi-compact, absolutely quasi-separated algebraic space known to be a
minimal nonscheme is irreducible. -/
instance instIsIrreducibleOfIsMinimalNonscheme {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] [Fact (IsMinimalNonscheme X)] :
    IsIrreducible X :=
  IsIrreducible.of_isMinimalNonscheme X Fact.out

end AlgebraicGeometry.AlgebraicSpace
