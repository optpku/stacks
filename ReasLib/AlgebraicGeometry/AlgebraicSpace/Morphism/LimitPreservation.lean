/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces over a scheme is locally of finite
presentation if and only if it is limit preserving as a transformation of
functors of points. -/
theorem locallyOfFinitePresentation_iff_isLimitPreserving
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    LocallyOfFinitePresentation f ↔ Scheme.Over.IsLimitPreserving f :=
  sorry

/-- A morphism of algebraic spaces over a scheme is locally of finite
presentation if the canonical comparison from the colimit of its source's
points to the relative fiber product is surjective on every directed inverse
limit of affine schemes over the base. -/
theorem locallyOfFinitePresentation_of_surjective_on_affine_stages
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hsurj :
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D)
        [HasColimit (D.op ⋙ X.functorOfPoints)]
        [HasColimit (D.op ⋙ Y.functorOfPoints)],
        IsLimit c →
          (∀ i : I, IsAffine (D.obj i).left) →
          IsAffine c.pt.left →
          ∀ x y,
            f.app (op c.pt) x =
                colimit.desc (D.op ⋙ Y.functorOfPoints)
                  (Y.functorOfPoints.mapCocone c.op) y →
              ∃ z,
                colimit.desc (D.op ⋙ X.functorOfPoints)
                    (X.functorOfPoints.mapCocone c.op) z = x ∧
                  colimMap (Functor.whiskerLeft D.op f) z = y) :
    LocallyOfFinitePresentation f :=
  sorry

/-- Surjectivity of the relative comparison on directed inverse limits of
affine schemes implies that a morphism of algebraic spaces is limit preserving
as a transformation of functors of points. -/
theorem isLimitPreserving_of_surjective_on_affine_stages
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hsurj :
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D)
        [HasColimit (D.op ⋙ X.functorOfPoints)]
        [HasColimit (D.op ⋙ Y.functorOfPoints)],
        IsLimit c →
          (∀ i : I, IsAffine (D.obj i).left) →
          IsAffine c.pt.left →
          ∀ x y,
            f.app (op c.pt) x =
                colimit.desc (D.op ⋙ Y.functorOfPoints)
                  (Y.functorOfPoints.mapCocone c.op) y →
              ∃ z,
                colimit.desc (D.op ⋙ X.functorOfPoints)
                    (X.functorOfPoints.mapCocone c.op) z = x ∧
                  colimMap (Functor.whiskerLeft D.op f) z = y) :
    Scheme.Over.IsLimitPreserving f :=
  (locallyOfFinitePresentation_iff_isLimitPreserving f).mp
    (locallyOfFinitePresentation_of_surjective_on_affine_stages f hsurj)

end AlgebraicGeometry.AlgebraicSpace
