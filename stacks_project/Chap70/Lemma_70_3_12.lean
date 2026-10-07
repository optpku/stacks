module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Whiskering
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap70.Definition_70_3_1

/-!
# Surjectivity of the fibre-product comparison implies locally of finite presentation

A morphism of algebraic spaces is locally of finite presentation as soon as
the functor-of-points comparison
`colim X(T_i) ⟶ X(T) ×_{Y(T)} colim Y(T_i)` is surjective on every directed
inverse limit of affine schemes over the base.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 70.3.12: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If for every directed inverse limit `T = lim T_i` of
affine schemes over `S` the comparison
`colim X(T_i) ⟶ X(T) ×_{Y(T)} colim Y(T_i)` is surjective, then `f` is locally
of finite presentation. In other words, in Proposition 70.3.10 part (2) it
suffices to check surjectivity in the criterion of Lemma 70.3.2. -/
@[stacks 0CM6]
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

/-- Surjectivity of the fibre-product comparison on directed inverse limits of
affine schemes over `S` implies that `f` is limit preserving as a transformation
of functors of points. -/
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
  sorry

end AlgebraicGeometry.AlgebraicSpace
