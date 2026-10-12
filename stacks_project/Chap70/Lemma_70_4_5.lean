/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap70.Definition_70_3_1

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

/-- Lemma 70.4.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. The equivalent conditions (1) and (2) of Proposition 70.3.10
are also equivalent to (3): for every directed inverse limit `T = lim T_i` of
quasi-compact and quasi-separated algebraic spaces `T_i` over `S` with affine
transition morphisms, the diagram of sets with maps
`colim Mor(T_i, X) ⟶ Mor(T, X)` and `colim Mor(T_i, Y) ⟶ Mor(T, Y)` is a fibre
product. -/
@[stacks 0CP4]
theorem locallyOfFinitePresentation_iff_isPullback_qcqsAffineLimits
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    LocallyOfFinitePresentation f ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D)
        [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
        [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
        [HasColimit (D.op ⋙ yoneda.obj X)] [HasColimit (D.op ⋙ yoneda.obj Y)],
        IsLimit c →
          IsPullback
            (colimit.desc (D.op ⋙ yoneda.obj X) ((yoneda.obj X).mapCocone c.op))
            (colimMap (Functor.whiskerLeft D.op (yoneda.map f)))
            ((yoneda.map f).app (op c.pt))
            (colimit.desc (D.op ⋙ yoneda.obj Y) ((yoneda.obj Y).mapCocone c.op)) :=
  sorry

/-- A morphism of algebraic spaces is limit preserving as a transformation of
functors if and only if it yields a fibre-product Hom-square on every directed
inverse limit of quasi-compact quasi-separated algebraic spaces with affine
transitions. -/
theorem isLimitPreserving_iff_isPullback_qcqsAffineLimits
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Scheme.Over.IsLimitPreserving f ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D)
        [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
        [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
        [HasColimit (D.op ⋙ yoneda.obj X)] [HasColimit (D.op ⋙ yoneda.obj Y)],
        IsLimit c →
          IsPullback
            (colimit.desc (D.op ⋙ yoneda.obj X) ((yoneda.obj X).mapCocone c.op))
            (colimMap (Functor.whiskerLeft D.op (yoneda.map f)))
            ((yoneda.map f).app (op c.pt))
            (colimit.desc (D.op ⋙ yoneda.obj Y) ((yoneda.obj Y).mapCocone c.op)) :=
  sorry

namespace LocallyOfFinitePresentation

/-- A locally of finite presentation morphism of algebraic spaces yields a
fibre-product Hom-square on every directed inverse limit of quasi-compact
quasi-separated algebraic spaces with affine transitions. -/
theorem isPullback_qcqsAffineLimits
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
    [HasColimit (D.op ⋙ yoneda.obj X)] [HasColimit (D.op ⋙ yoneda.obj Y)] :
    IsPullback
      (colimit.desc (D.op ⋙ yoneda.obj X) ((yoneda.obj X).mapCocone c.op))
      (colimMap (Functor.whiskerLeft D.op (yoneda.map f)))
      ((yoneda.map f).app (op c.pt))
      (colimit.desc (D.op ⋙ yoneda.obj Y) ((yoneda.obj Y).mapCocone c.op)) :=
  sorry

end LocallyOfFinitePresentation

/-- A morphism of algebraic spaces is locally of finite presentation if it
yields a fibre-product Hom-square on every directed inverse limit of
quasi-compact quasi-separated algebraic spaces with affine transitions. -/
theorem locallyOfFinitePresentation_of_isPullback_qcqsAffineLimits
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hsq :
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D)
        [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
        [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
        [HasColimit (D.op ⋙ yoneda.obj X)] [HasColimit (D.op ⋙ yoneda.obj Y)],
        IsLimit c →
          IsPullback
            (colimit.desc (D.op ⋙ yoneda.obj X) ((yoneda.obj X).mapCocone c.op))
            (colimMap (Functor.whiskerLeft D.op (yoneda.map f)))
            ((yoneda.map f).app (op c.pt))
            (colimit.desc (D.op ⋙ yoneda.obj Y) ((yoneda.obj Y).mapCocone c.op))) :
    LocallyOfFinitePresentation f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
