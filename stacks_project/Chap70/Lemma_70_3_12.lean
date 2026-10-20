module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LimitPreservation
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

/- Lemma 70.3.12: Surjectivity of the relative comparison on directed inverse
limits of affine schemes implies local finite presentation. -/
@[stacks 0CM6] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_of_surjective_on_affine_stages :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
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
                  colimMap (Functor.whiskerLeft D.op f) z = y),
    AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation f)

#check
  (AlgebraicGeometry.AlgebraicSpace.isLimitPreserving_of_surjective_on_affine_stages :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
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
                  colimMap (Functor.whiskerLeft D.op f) z = y),
    Scheme.Over.IsLimitPreserving f)
