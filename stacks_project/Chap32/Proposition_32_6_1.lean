module

import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation.Yoneda
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/- Proposition 32.6.1: A scheme morphism is locally of finite presentation if and only if
its functor of points preserves every directed inverse limit with affine stages. -/
@[stacks 01ZC] #check
  (AlgebraicGeometry.Scheme.Over.Yoneda.locallyFinitePresentation_iff :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.LocallyOfFinitePresentation f ↔
        AlgebraicGeometry.Scheme.Over.PreservesDirectedAffineLimits S
          (yoneda.obj (Over.mk f)))

#check
  (AlgebraicGeometry.Scheme.Over.Yoneda.locallyFinitePresentation_iff_qcqsAffineTransition :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.LocallyOfFinitePresentation f ↔
        ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
          (D : OrderDual I ⥤ Over S) (c : Cone D),
            IsLimit c →
            (∀ {i i' : I} (hii' : i ≤ i'),
              AlgebraicGeometry.IsAffineHom (D.map (homOfLE hii')).left) →
            (∀ i : I, CompactSpace (D.obj i).left) →
            (∀ i : I, QuasiSeparatedSpace (D.obj i).left) →
            Nonempty (IsColimit ((yoneda.obj (Over.mk f)).mapCocone c.op)))
