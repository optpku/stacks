module

import Mathlib.AlgebraicGeometry.AffineTransitionLimit

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation

/-!
# Limit preservation of a scheme's functor of points

This leaf records the canonical bridges between local finite presentation of a
scheme morphism and preservation by its functor of points of directed affine
limits, as well as directed limits with affine transition morphisms and
quasi-compact, quasi-separated stages. The underlying affine-limit-preservation
predicate lives in the sibling `Preservation` leaf and is independent of
representability.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Over.Yoneda

/-- If the functor of points of a scheme morphism sends every directed inverse limit
of affine schemes over the target to a surjection from the colimit of its values,
then the morphism is locally of finite presentation. -/
theorem locallyFinitePresentation_of_surjective_on_affine_stages
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hsurj :
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D),
          IsLimit c →
          (∀ i : I, IsAffine (D.obj i).left) →
          Function.Surjective
            (colimit.desc _ ((yoneda.obj (Over.mk f)).mapCocone c.op))) :
    LocallyOfFinitePresentation f := sorry

/-- A scheme morphism is locally of finite presentation exactly when its functor of
points preserves directed affine limits over the target. -/
@[stacks 05LX]
theorem locallyFinitePresentation_iff
    {X S : Scheme.{u}} (f : X ⟶ S) :
    LocallyOfFinitePresentation f ↔
      Scheme.Over.PreservesDirectedAffineLimits S (yoneda.obj (Over.mk f)) := sorry

/-- The functor of points of a locally finitely presented scheme preserves directed
affine limits over its base. -/
theorem preserves_of_locallyFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] :
    Scheme.Over.PreservesDirectedAffineLimits S (yoneda.obj (Over.mk f)) := sorry

/-- A scheme morphism is locally of finite presentation exactly when its functor of
points preserves directed limits whose transition morphisms are affine and whose
stages are quasi-compact and quasi-separated. -/
theorem locallyFinitePresentation_iff_qcqsAffineTransition
    {X S : Scheme.{u}} (f : X ⟶ S) :
    LocallyOfFinitePresentation f ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D),
          IsLimit c →
          (∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii')).left) →
          (∀ i : I, CompactSpace (D.obj i).left) →
          (∀ i : I, QuasiSeparatedSpace (D.obj i).left) →
          Nonempty (IsColimit ((yoneda.obj (Over.mk f)).mapCocone c.op)) := sorry

end AlgebraicGeometry.Scheme.Over.Yoneda
