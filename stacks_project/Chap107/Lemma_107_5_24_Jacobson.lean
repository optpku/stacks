/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.JacobsonSpace
public import stacks_project.Chap100.Lemma_100_7_1_SmoothLocal
public import stacks_project.Chap101.Definition_101_13_2_Closed

/-!
# Jacobson and irreducible algebraic stacks

An algebraic stack is Jacobson when it admits a surjective smooth atlas from a
Jacobson scheme. It is irreducible when every canonical topology on its points
is an irreducible space.
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

/-- An algebraic stack is irreducible when every canonical topology on `|X|` is
an irreducible space. -/
@[mk_iff]
class IsIrreducible {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    Prop where
  /-- Every canonical topology on `|X|` is an irreducible space. -/
  irreducibleSpace :
    ∀ (τ : TopologicalSpace (Points X)),
      IsPointsTopology X τ → @IrreducibleSpace (Points X) τ

namespace IsIrreducible

/-- An irreducible algebraic stack has irreducible underlying point space in
every canonical topology. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsIrreducible X] {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) : @IrreducibleSpace (Points X) τ :=
  sorry

/-- Irreducibility of every canonical topology on `|X|` witnesses
`IsIrreducible`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : ∀ (τ : TopologicalSpace (Points X)),
      IsPointsTopology X τ → @IrreducibleSpace (Points X) τ) :
    IsIrreducible X :=
  sorry

end IsIrreducible

/-- The canonical slice of an irreducible scheme over `S` is an irreducible
algebraic stack. -/
instance instIsIrreducible_slice {S : Scheme.{u}} (U : Over S)
    [IrreducibleSpace U.left] : IsIrreducible (GroupoidsOver.slice U) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
