module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation.Yoneda
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

/- A set-valued presheaf on `(Over S)ᵒᵖ` preserves directed affine inverse
limits when its induced cocone on values is a colimit. -/
#check
  (AlgebraicGeometry.Scheme.Over.PreservesDirectedAffineLimits :
    ∀ (S : AlgebraicGeometry.Scheme.{u}), ((Over S)ᵒᵖ ⥤ Type v) → Prop)

#check
  (AlgebraicGeometry.Scheme.Over.preservesDirectedAffineLimits_iff :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type v),
      AlgebraicGeometry.Scheme.Over.PreservesDirectedAffineLimits S F ↔
        ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
          (D : OrderDual I ⥤ Over S) (c : Cone D),
            IsLimit c →
            (∀ i : I, AlgebraicGeometry.IsAffine (D.obj i).left) →
            AlgebraicGeometry.IsAffine c.pt.left →
            Nonempty (IsColimit (F.mapCocone c.op)))

#check
  (AlgebraicGeometry.Scheme.Over.preservesDirectedAffineLimits_iff_affine_stages :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type v),
      AlgebraicGeometry.Scheme.Over.PreservesDirectedAffineLimits S F ↔
        ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
          (D : OrderDual I ⥤ Over S) (c : Cone D),
            IsLimit c →
            (∀ i : I, AlgebraicGeometry.IsAffine (D.obj i).left) →
            Nonempty (IsColimit (F.mapCocone c.op)))

/- Remark 32.6.2: the functor of points of `f : X ⟶ S`
preserves directed affine limits exactly when `f` is locally of finite
presentation. -/
@[stacks 05LX] #check
  (AlgebraicGeometry.Scheme.Over.Yoneda.locallyFinitePresentation_iff :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.LocallyOfFinitePresentation f ↔
        AlgebraicGeometry.Scheme.Over.PreservesDirectedAffineLimits S
          (yoneda.obj (Over.mk f)))

#check
  (AlgebraicGeometry.Scheme.Over.Yoneda.preserves_of_locallyFinitePresentation :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFinitePresentation f],
        AlgebraicGeometry.Scheme.Over.PreservesDirectedAffineLimits S
          (yoneda.obj (Over.mk f)))
