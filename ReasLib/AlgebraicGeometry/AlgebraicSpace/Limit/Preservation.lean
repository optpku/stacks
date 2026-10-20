module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver

/-!
# Preservation of directed affine limits on schemes over an algebraic space

A set-valued presheaf on schemes over a fixed algebraic space preserves
directed affine limits when it carries their limit cones to colimit cocones
of sets.
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
