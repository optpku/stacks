module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LimitPreservation.Qcqs
import StacksCheckRecall

/-!
# Characterisation of locally of finite presentation via qcqs affine-transition limits

For a morphism of algebraic spaces over a scheme, the following three conditions
are equivalent: being locally of finite presentation, being limit preserving as
a transformation of functors of points, and yielding a fibre-product Hom-square
on every directed inverse limit of quasi-compact quasi-separated algebraic spaces
with affine transition morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

/- Lemma 70.4.5: The local finite presentation and relative limit preservation
conditions are also equivalent to the canonical Hom-square being a fibre product
for every directed inverse limit of quasi-compact quasi-separated algebraic spaces
with affine transition morphisms. -/
@[stacks 0CP4]
#check
  (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_iff_isPullback_qcqsAffineLimits :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      AlgebraicSpace.LocallyOfFinitePresentation f ↔
        ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
          (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D)
          [∀ {i i' : I} (h : i ≤ i'), AlgebraicSpace.Affine (D.map (homOfLE h))]
          [∀ i, AlgebraicSpace.IsQuasiCompact (D.obj i)]
          [∀ i, AlgebraicSpace.IsAbsolutelyQuasiSeparated (D.obj i)],
          IsLimit c →
            IsPullback
              (colimit.desc (D.op ⋙ yoneda.obj X) ((yoneda.obj X).mapCocone c.op))
              (colimMap (Functor.whiskerLeft D.op (yoneda.map f)))
              ((yoneda.map f).app (op c.pt))
              (colimit.desc (D.op ⋙ yoneda.obj Y) ((yoneda.obj Y).mapCocone c.op)))
