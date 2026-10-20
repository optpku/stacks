/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic

/-!
# Quasi-compact algebraic stacks

An algebraic stack is quasi-compact when it admits a surjective smooth atlas
from a quasi-compact scheme. This is equivalent to quasi-compactness of its
topological space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack is quasi-compact if it admits a surjective smooth atlas
from a quasi-compact scheme. -/
@[mk_iff]
class IsQuasiCompact {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] : Prop where
  /-- There is a surjective smooth 1-morphism from the slice of a quasi-compact scheme. -/
  exists_compact_smooth_cover :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ CompactSpace U.left

namespace IsQuasiCompact

/-- A quasi-compact algebraic stack admits a surjective smooth atlas from a
quasi-compact scheme. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsQuasiCompact X] :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ CompactSpace U.left :=
  sorry

/-- A surjective smooth atlas from a quasi-compact scheme witnesses that the
algebraic stack is quasi-compact. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [CompactSpace U.left] : IsQuasiCompact X :=
  sorry

end IsQuasiCompact

/-- The canonical slice of a quasi-compact scheme over `S` is a quasi-compact
algebraic stack. -/
instance instIsQuasiCompact_slice {S : Scheme.{u}} (U : Over S)
    [CompactSpace U.left] : IsQuasiCompact (GroupoidsOver.slice U) where
  exists_compact_smooth_cover :=
    ⟨U, 𝟙 (GroupoidsOver.slice U), inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry.AlgebraicStack
