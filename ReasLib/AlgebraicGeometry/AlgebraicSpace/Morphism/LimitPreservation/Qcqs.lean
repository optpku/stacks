module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LimitPreservation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Characterisation of locally of finite presentation via qcqs affine-transition limits

A morphism of algebraic spaces is locally of finite presentation if and only if
it yields a fibre-product square of Hom-sets on every directed inverse limit of
quasi-compact quasi-separated algebraic spaces with affine transitions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces over a scheme is locally of finite presentation
if and only if its canonical Hom-square is a pullback on every directed inverse
limit of quasi-compact, absolutely quasi-separated algebraic spaces with affine
transition morphisms. -/
theorem locallyOfFinitePresentation_iff_isPullback_qcqsAffineLimits
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    LocallyOfFinitePresentation f ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D)
        [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
        [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsAbsolutelyQuasiSeparated (D.obj i)],
        IsLimit c →
          IsPullback
            (colimit.desc (D.op ⋙ yoneda.obj X) ((yoneda.obj X).mapCocone c.op))
            (colimMap (Functor.whiskerLeft D.op (yoneda.map f)))
            ((yoneda.map f).app (op c.pt))
            (colimit.desc (D.op ⋙ yoneda.obj Y) ((yoneda.obj Y).mapCocone c.op)) :=
  sorry

/-- A morphism of algebraic spaces is limit preserving as a transformation of
functors if and only if it yields a fibre-product Hom-square on every directed
inverse limit of quasi-compact, absolutely quasi-separated algebraic spaces with affine
transitions. -/
theorem isLimitPreserving_iff_isPullback_qcqsAffineLimits
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Scheme.Over.IsLimitPreserving f ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D)
        [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
        [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsAbsolutelyQuasiSeparated (D.obj i)],
        IsLimit c →
          IsPullback
            (colimit.desc (D.op ⋙ yoneda.obj X) ((yoneda.obj X).mapCocone c.op))
            (colimMap (Functor.whiskerLeft D.op (yoneda.map f)))
            ((yoneda.map f).app (op c.pt))
            (colimit.desc (D.op ⋙ yoneda.obj Y) ((yoneda.obj Y).mapCocone c.op)) :=
  (locallyOfFinitePresentation_iff_isLimitPreserving f).symm.trans
    (locallyOfFinitePresentation_iff_isPullback_qcqsAffineLimits f)

namespace LocallyOfFinitePresentation

/-- A locally of finite presentation morphism of algebraic spaces yields a
fibre-product Hom-square on every directed inverse limit of quasi-compact,
absolutely quasi-separated algebraic spaces with affine transitions. -/
theorem isPullback_qcqsAffineLimits
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsAbsolutelyQuasiSeparated (D.obj i)] :
    IsPullback
      (colimit.desc (D.op ⋙ yoneda.obj X) ((yoneda.obj X).mapCocone c.op))
      (colimMap (Functor.whiskerLeft D.op (yoneda.map f)))
      ((yoneda.map f).app (op c.pt))
      (colimit.desc (D.op ⋙ yoneda.obj Y) ((yoneda.obj Y).mapCocone c.op)) :=
  (locallyOfFinitePresentation_iff_isPullback_qcqsAffineLimits f).mp
    inferInstance D c hc

end LocallyOfFinitePresentation

/-- A morphism of algebraic spaces is locally of finite presentation if it
yields a fibre-product Hom-square on every directed inverse limit of
quasi-compact, absolutely quasi-separated algebraic spaces with affine transitions. -/
theorem locallyOfFinitePresentation_of_isPullback_qcqsAffineLimits
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hsq :
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D)
        [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
        [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsAbsolutelyQuasiSeparated (D.obj i)],
        IsLimit c →
          IsPullback
            (colimit.desc (D.op ⋙ yoneda.obj X) ((yoneda.obj X).mapCocone c.op))
            (colimMap (Functor.whiskerLeft D.op (yoneda.map f)))
            ((yoneda.map f).app (op c.pt))
            (colimit.desc (D.op ⋙ yoneda.obj Y) ((yoneda.obj Y).mapCocone c.op))) :
    LocallyOfFinitePresentation f :=
  (locallyOfFinitePresentation_iff_isPullback_qcqsAffineLimits f).mpr hsq

end AlgebraicGeometry.AlgebraicSpace
