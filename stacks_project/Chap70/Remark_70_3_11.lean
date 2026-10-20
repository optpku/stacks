module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LimitPreservation.ToBase
import StacksCheckRecall

/-!
# Locally of finite presentation of an algebraic space over its base

An algebraic space `X` over a scheme `S` is locally of finite presentation over
`S` if and only if its functor of points preserves directed affine limits.
Surjectivity of the comparison `colim X(T_i) ⟶ X(T)` on directed inverse limits
of affine schemes over `S` already implies that property.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Remark 70.3.11 (1): Let `S` be a scheme. Let `X` be an algebraic space over
`S`. Then `X` is locally of finite presentation over `S` if and only if `X`, as
a functor `(Over S)ᵒᵖ ⥤ Type`, is limit preserving. Compare with Limits,
Remark 32.6.2. -/
@[stacks 05N0] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_iff_preservesDirectedAffineLimits :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
      LocallyOfFinitePresentation (SchemeRealization.toBase X) ↔
        Scheme.Over.PreservesDirectedAffineLimits S X.functorOfPoints)

/- Remark 70.3.11 (2): In the criterion of Remark 70.3.11 (1), it suffices that
the comparison `colim X(T_i) ⟶ X(T)` is surjective whenever `T = lim T_i` is a
directed inverse limit of affine schemes over `S`. -/
@[stacks 05N0] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_toBase_of_surjective_on_affine_stages :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hsurj :
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D),
        IsLimit c →
          (∀ i : I, IsAffine (D.obj i).left) →
          Function.Surjective
            (colimit.desc (D.op ⋙ X.functorOfPoints)
              (X.functorOfPoints.mapCocone c.op))),
      LocallyOfFinitePresentation (SchemeRealization.toBase X))

#check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation.preservesDirectedAffineLimits_toBase :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [LocallyOfFinitePresentation (SchemeRealization.toBase X)],
      Scheme.Over.PreservesDirectedAffineLimits S X.functorOfPoints)

#check
  (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_of_preservesDirectedAffineLimits :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
      Scheme.Over.PreservesDirectedAffineLimits S X.functorOfPoints →
        LocallyOfFinitePresentation (SchemeRealization.toBase X))

#check (AlgebraicGeometry.AlgebraicSpace.isLimitPreserving_toBase_iff :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    Scheme.Over.IsLimitPreserving (SchemeRealization.toBase X) ↔
      Scheme.Over.PreservesDirectedAffineLimits S X.functorOfPoints)

end AlgebraicGeometry.AlgebraicSpace
