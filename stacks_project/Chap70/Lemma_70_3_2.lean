/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation.Pullback
import StacksCheckRecall

/-!
# Characterisation of relatively limit-preserving transformations

A transformation of set-valued functors on schemes over a base is limit
preserving if and only if it yields a fibre-product square of sets on every
directed inverse limit of affine schemes over that base.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Over

/- Lemma 70.3.2: Let `S` be a scheme. Let `a : F ⟶ G` be a transformation of
functors `(Over S)ᵒᵖ ⥤ Type`. The following are equivalent: `a` is limit
preserving, and for every affine scheme `T` over `S` which is a directed inverse
limit `T = lim T_i` of affine schemes `T_i` over `S`, the diagram of sets with
maps `colim F(T_i) ⟶ F(T)` and `colim G(T_i) ⟶ G(T)` is a fibre product. -/
@[stacks 06BC] #check
  (AlgebraicGeometry.Scheme.Over.isLimitPreserving_iff_isPullback :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type (max u v)} (a : F ⟶ G),
    IsLimitPreserving a ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D),
        IsLimit c →
          (∀ i : I, IsAffine (D.obj i).left) →
          IsAffine c.pt.left →
          IsPullback (colimit.desc (D.op ⋙ F) (F.mapCocone c.op))
            (colimMap (Functor.whiskerLeft D.op a)) (a.app (op c.pt))
            (colimit.desc (D.op ⋙ G) (G.mapCocone c.op)))

#check
  (AlgebraicGeometry.Scheme.Over.IsLimitPreserving.isPullback :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type (max u v)}
    {a : F ⟶ G}, IsLimitPreserving a →
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D),
    IsLimit c → (∀ i : I, IsAffine (D.obj i).left) →
    IsAffine c.pt.left →
    IsPullback (colimit.desc (D.op ⋙ F) (F.mapCocone c.op))
      (colimMap (Functor.whiskerLeft D.op a)) (a.app (op c.pt))
      (colimit.desc (D.op ⋙ G) (G.mapCocone c.op)))

#check
  (AlgebraicGeometry.Scheme.Over.isLimitPreserving_of_isPullback :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type (max u v)}
    {a : F ⟶ G},
    (∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Over S) (c : Cone D),
      IsLimit c →
        (∀ i : I, IsAffine (D.obj i).left) →
        IsAffine c.pt.left →
        IsPullback (colimit.desc (D.op ⋙ F) (F.mapCocone c.op))
          (colimMap (Functor.whiskerLeft D.op a)) (a.app (op c.pt))
          (colimit.desc (D.op ⋙ G) (G.mapCocone c.op))) →
    IsLimitPreserving a)

end AlgebraicGeometry.Scheme.Over
