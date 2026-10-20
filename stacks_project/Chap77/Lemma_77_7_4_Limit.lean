module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.Preservation

/-!
# Preservation of directed affine limits on schemes over an algebraic space

The preservation predicate and its diagrammatic characterizations for
set-valued presheaves on schemes over an algebraic space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.SchemeOver

universe u v

#check (AlgebraicGeometry.AlgebraicSpace.SchemeOver.PreservesDirectedAffineLimits :
    ∀ {S : Scheme.{u}} (B : AlgebraicSpace S)
      (F : (SchemeOver B)ᵒᵖ ⥤ Type v), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.SchemeOver.preservesDirectedAffineLimits_iff :
    ∀ {S : Scheme.{u}} (B : AlgebraicSpace S)
    (F : (SchemeOver B)ᵒᵖ ⥤ Type v),
    PreservesDirectedAffineLimits B F ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ SchemeOver B) (c : Cone D),
          IsLimit c →
          (∀ i : I, IsAffine (D.obj i).left.left) →
          IsAffine c.pt.left.left →
          Nonempty (IsColimit (F.mapCocone c.op)))

#check (AlgebraicGeometry.AlgebraicSpace.SchemeOver.preservesDirectedAffineLimits_iff_affine_stages :
    ∀ {S : Scheme.{u}}
    (B : AlgebraicSpace S) (F : (SchemeOver B)ᵒᵖ ⥤ Type v),
    PreservesDirectedAffineLimits B F ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ SchemeOver B) (c : Cone D),
          IsLimit c →
          (∀ i : I, IsAffine (D.obj i).left.left) →
          Nonempty (IsColimit (F.mapCocone c.op)))
