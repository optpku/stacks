/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap87.Definition_87_25_1_Surjective
public import stacks_project.Chap87.FormalAlgebraicSpace.Yoneda

/-!
# Quasi-compact formal algebraic spaces

A formal algebraic space is quasi-compact when its algebraic-space reduction
is a quasi-compact algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A formal algebraic space is quasi-compact if its algebraic-space reduction
is a quasi-compact algebraic space. -/
@[mk_iff]
class IsQuasiCompact {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [Reduction X] : Prop where
  /-- The reduction of `X` is a quasi-compact algebraic space. -/
  isQuasiCompact_reduction : AlgebraicSpace.IsQuasiCompact (reduction X)

namespace IsQuasiCompact

/-- A quasi-compact formal algebraic space has quasi-compact algebraic-space
reduction. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [Reduction X] [IsQuasiCompact X] :
    AlgebraicSpace.IsQuasiCompact (reduction X) :=
  sorry

/-- Quasi-compactness of the algebraic-space reduction witnesses that a formal
algebraic space is quasi-compact. -/
theorem of {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X]
    (h : AlgebraicSpace.IsQuasiCompact (reduction X)) : IsQuasiCompact X :=
  sorry

/-- A formal algebraic space is quasi-compact if and only if its reduction is a
quasi-compact algebraic space. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [Reduction X] :
    IsQuasiCompact X ↔ AlgebraicSpace.IsQuasiCompact (reduction X) :=
  sorry

end IsQuasiCompact

/-- A quasi-compact algebraic space is quasi-compact as a formal algebraic
space, via its functor of points. -/
instance instIsQuasiCompact_functorOfPoints {S : Scheme.{u}}
    (X : AlgebraicSpace S) [AlgebraicSpace.IsQuasiCompact X]
    [Reduction X.functorOfPoints] : IsQuasiCompact X.functorOfPoints :=
  sorry

/-- A quasi-compact scheme over `S`, viewed as a formal algebraic space, is
quasi-compact. -/
instance instIsQuasiCompact_yoneda {S : Scheme.{u}} (T : Over S)
    [CompactSpace T.left] [Reduction (yoneda.obj T)] :
    IsQuasiCompact (yoneda.obj T) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
