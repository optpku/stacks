module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LimitPreservation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Limit preservation over the base of an algebraic space

Local finite presentation of an algebraic space over its base is equivalent to
preservation of directed affine limits by its functor of points. Surjectivity
of the canonical comparison on these limits already suffices.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structural morphism of an algebraic space is limit preserving if and
only if its functor of points preserves directed affine limits. -/
theorem isLimitPreserving_toBase_iff {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Scheme.Over.IsLimitPreserving (SchemeRealization.toBase X) ↔
      Scheme.Over.PreservesDirectedAffineLimits S X.functorOfPoints :=
  sorry

/-- An algebraic space is locally of finite presentation over its base if and
only if its functor of points preserves directed affine limits. -/
theorem locallyOfFinitePresentation_iff_preservesDirectedAffineLimits
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    LocallyOfFinitePresentation (SchemeRealization.toBase X) ↔
      Scheme.Over.PreservesDirectedAffineLimits S X.functorOfPoints :=
  (locallyOfFinitePresentation_iff_isLimitPreserving (SchemeRealization.toBase X)).trans
    (isLimitPreserving_toBase_iff X)

namespace LocallyOfFinitePresentation

/-- An algebraic space locally of finite presentation over its base has a
functor of points that preserves directed affine limits. -/
theorem preservesDirectedAffineLimits_toBase {S : Scheme.{u}} (X : AlgebraicSpace S)
    [LocallyOfFinitePresentation (SchemeRealization.toBase X)] :
    Scheme.Over.PreservesDirectedAffineLimits S X.functorOfPoints :=
  (locallyOfFinitePresentation_iff_preservesDirectedAffineLimits X).mp inferInstance

end LocallyOfFinitePresentation

/-- If the functor of points of an algebraic space preserves directed affine
limits, then its structural morphism is locally of finite presentation. -/
theorem locallyOfFinitePresentation_of_preservesDirectedAffineLimits
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : Scheme.Over.PreservesDirectedAffineLimits S X.functorOfPoints) :
    LocallyOfFinitePresentation (SchemeRealization.toBase X) :=
  (locallyOfFinitePresentation_iff_preservesDirectedAffineLimits X).mpr h

/-- An algebraic space is locally of finite presentation over its base if the
canonical comparison from the colimit of its points on the stages to its
points on the limit is surjective for every directed inverse limit of affine
schemes over the base. -/
theorem locallyOfFinitePresentation_toBase_of_surjective_on_affine_stages
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hsurj :
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D),
        IsLimit c →
          (∀ i : I, IsAffine (D.obj i).left) →
          Function.Surjective
            (colimit.desc (D.op ⋙ X.functorOfPoints)
              (X.functorOfPoints.mapCocone c.op))) :
    LocallyOfFinitePresentation (SchemeRealization.toBase X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
