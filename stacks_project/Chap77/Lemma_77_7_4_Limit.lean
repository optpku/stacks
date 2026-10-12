/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Order.Directed
public import stacks_project.Chap77.«77_7_1_1_IsomorphismFunctor»

/-!
# Preservation of directed affine limits on schemes over an algebraic space

This leaf owns the condition that a set-valued presheaf on schemes over a
fixed algebraic space `B` carries directed inverse limits of affine schemes
to colimits of sets.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.SchemeOver

/-- A presheaf on `SchemeOver B` preserves directed inverse limits of affine
schemes over `B`. -/
def PreservesDirectedAffineLimits {S : Scheme.{u}} (B : AlgebraicSpace S)
    (F : (SchemeOver B)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ SchemeOver B) (c : Cone D),
      IsLimit c →
      (∀ i : I, IsAffine (D.obj i).left.left) →
      IsAffine c.pt.left.left →
      Nonempty (IsColimit (F.mapCocone c.op))

/-- The directed-affine-limit condition on schemes over `B` unfolds to its
diagrammatic form. -/
theorem preservesDirectedAffineLimits_iff {S : Scheme.{u}} (B : AlgebraicSpace S)
    (F : (SchemeOver B)ᵒᵖ ⥤ Type v) :
    PreservesDirectedAffineLimits B F ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ SchemeOver B) (c : Cone D),
          IsLimit c →
          (∀ i : I, IsAffine (D.obj i).left.left) →
          IsAffine c.pt.left.left →
          Nonempty (IsColimit (F.mapCocone c.op)) := sorry

/-- For a directed inverse system of affine schemes over `B`, the limit cone
point is affine, so the target-affineness hypothesis in
`PreservesDirectedAffineLimits` is redundant. -/
theorem preservesDirectedAffineLimits_iff_affine_stages {S : Scheme.{u}}
    (B : AlgebraicSpace S) (F : (SchemeOver B)ᵒᵖ ⥤ Type v) :
    PreservesDirectedAffineLimits B F ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ SchemeOver B) (c : Cone D),
          IsLimit c →
          (∀ i : I, IsAffine (D.obj i).left.left) →
          Nonempty (IsColimit (F.mapCocone c.op)) := sorry

end AlgebraicGeometry.AlgebraicSpace.SchemeOver
