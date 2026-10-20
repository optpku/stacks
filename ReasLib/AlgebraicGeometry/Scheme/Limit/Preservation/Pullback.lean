module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Whiskering

/-!
# Pullback characterization of relative limit preservation

A transformation of set-valued presheaves on schemes over a base preserves
directed affine limits fiberwise exactly when its comparison squares are
pullbacks.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Over

/-- A transformation of presheaves on schemes over a base is limit preserving
if and only if every directed inverse limit of affine schemes induces a
pullback square of sets. -/
theorem isLimitPreserving_iff_isPullback {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type (max u v)} (a : F ⟶ G) :
    IsLimitPreserving a ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D),
        IsLimit c →
          (∀ i : I, IsAffine (D.obj i).left) →
          IsAffine c.pt.left →
          IsPullback (colimit.desc (D.op ⋙ F) (F.mapCocone c.op))
            (colimMap (Functor.whiskerLeft D.op a)) (a.app (op c.pt))
            (colimit.desc (D.op ⋙ G) (G.mapCocone c.op)) :=
  sorry

/-- A limit-preserving transformation yields a pullback square of sets on
every directed inverse limit of affine schemes over its base. -/
theorem IsLimitPreserving.isPullback {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type (max u v)}
    {a : F ⟶ G} (ha : IsLimitPreserving a)
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D)
    (hc : IsLimit c) (hD : ∀ i : I, IsAffine (D.obj i).left)
    (hT : IsAffine c.pt.left) :
    IsPullback (colimit.desc (D.op ⋙ F) (F.mapCocone c.op))
      (colimMap (Functor.whiskerLeft D.op a)) (a.app (op c.pt))
      (colimit.desc (D.op ⋙ G) (G.mapCocone c.op)) :=
  (isLimitPreserving_iff_isPullback a).mp ha D c hc hD hT

/-- A transformation is limit preserving if every directed inverse limit of
affine schemes over its base yields a pullback square of sets. -/
theorem isLimitPreserving_of_isPullback {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type (max u v)}
    {a : F ⟶ G}
    (h : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Over S) (c : Cone D),
      IsLimit c →
        (∀ i : I, IsAffine (D.obj i).left) →
        IsAffine c.pt.left →
        IsPullback (colimit.desc (D.op ⋙ F) (F.mapCocone c.op))
          (colimMap (Functor.whiskerLeft D.op a)) (a.app (op c.pt))
          (colimit.desc (D.op ⋙ G) (G.mapCocone c.op))) :
    IsLimitPreserving a :=
  (isLimitPreserving_iff_isPullback a).mpr h

namespace IsLimitPreserving

/-- A pullback square of transformations preserves limits after composing with
the common target whenever the three comparison transformations do. -/
theorem pullback_comp {S : Scheme.{u}} {E F G H P : (Over S)ᵒᵖ ⥤ Type v}
    {a : F ⟶ G} {b : H ⟶ G} {c : G ⟶ E} {a' : P ⟶ H} {b' : P ⟶ F}
    (sq : IsPullback b' a' a b) (hc : IsLimitPreserving c)
    (hac : IsLimitPreserving (a ≫ c)) (hbc : IsLimitPreserving (b ≫ c)) :
    IsLimitPreserving (b' ≫ a ≫ c) := sorry

/-- The first projection from a chosen pullback preserves limits after
composing with the common target whenever the three comparison transformations
do. -/
theorem pullback_fst_comp {S : Scheme.{u}} {E F G H : (Over S)ᵒᵖ ⥤ Type v}
    {a : F ⟶ G} {b : H ⟶ G} {c : G ⟶ E} [HasPullback a b]
    (hc : IsLimitPreserving c) (hac : IsLimitPreserving (a ≫ c))
    (hbc : IsLimitPreserving (b ≫ c)) :
    IsLimitPreserving (pullback.fst a b ≫ a ≫ c) := sorry

end IsLimitPreserving

end AlgebraicGeometry.Scheme.Over
