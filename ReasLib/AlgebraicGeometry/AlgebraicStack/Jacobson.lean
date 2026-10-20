/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.AlgebraicStack.SmoothLocal

/-!
# Jacobson algebraic stacks

Jacobsonness is defined by a smooth surjective atlas from a Jacobson scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack is Jacobson if it admits a surjective smooth atlas whose
source is a Jacobson scheme. -/
@[mk_iff]
class IsJacobson {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    Prop where
  /-- There is a surjective smooth 1-morphism from the slice of a Jacobson
  scheme. -/
  exists_jacobson_smooth_cover :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ JacobsonSpace U.left

namespace IsJacobson

/-- A Jacobson algebraic stack admits a surjective smooth atlas from a Jacobson
scheme. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsJacobson X] :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        JacobsonSpace U.left :=
  sorry

/-- A surjective smooth atlas from a Jacobson scheme witnesses that the
algebraic stack is Jacobson. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [JacobsonSpace U.left] :
    IsJacobson X :=
  sorry

end IsJacobson

/-- The canonical slice of a Jacobson scheme over `S` is a Jacobson algebraic
stack. -/
instance instIsJacobson_slice {S : Scheme.{u}} (U : Over S)
    [JacobsonSpace U.left] : IsJacobson (GroupoidsOver.slice U) where
  exists_jacobson_smooth_cover :=
    ⟨U, 𝟙 (GroupoidsOver.slice U), inferInstance, inferInstance, inferInstance⟩

/-- An algebraic stack is Jacobson if and only if it admits a surjective smooth
scheme atlas whose source is Jacobson. -/
theorem isJacobson_iff_existsSurjectiveSmooth {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    IsJacobson X ↔
      existsSurjectiveSmooth (fun U : Scheme.{u} ↦ JacobsonSpace U) X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
