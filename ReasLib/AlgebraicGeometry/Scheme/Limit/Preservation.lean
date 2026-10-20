module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.Scheme.Presheaf.Fiber

/-!
# Preservation of directed affine limits

This leaf owns the condition that a set-valued presheaf on schemes over a
fixed base carries directed inverse limits of affine schemes to colimits of
sets.  It is independent of a choice of site or extension construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

namespace Scheme.Over

/-- A presheaf on `Over S` preserves directed limits of affine schemes over
`S`. -/
def PreservesDirectedAffineLimits (S : Scheme.{u})
    (F : (Over S)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D),
      IsLimit c →
      (∀ i : I, IsAffine (D.obj i).left) →
      IsAffine c.pt.left →
      Nonempty (IsColimit (F.mapCocone c.op))

/-- The directed-affine-limit condition on all schemes over `S` unfolds to its
diagrammatic form. -/
theorem preservesDirectedAffineLimits_iff (S : Scheme.{u})
    (F : (Over S)ᵒᵖ ⥤ Type v) :
    PreservesDirectedAffineLimits S F ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D),
          IsLimit c →
          (∀ i : I, IsAffine (D.obj i).left) →
          IsAffine c.pt.left →
          Nonempty (IsColimit (F.mapCocone c.op)) := sorry

/-- For a directed inverse system of affine schemes over `S`, the limit cone
point is affine by `Scheme.isAffine_of_isLimit`; thus the target-affineness
hypothesis in `PreservesDirectedAffineLimits` is redundant. -/
theorem preservesDirectedAffineLimits_iff_affine_stages (S : Scheme.{u})
    (F : (Over S)ᵒᵖ ⥤ Type v) :
    PreservesDirectedAffineLimits S F ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D),
          IsLimit c →
      (∀ i : I, IsAffine (D.obj i).left) →
          Nonempty (IsColimit (F.mapCocone c.op)) := sorry

/-! The relative limit-preservation condition is defined by applying the
absolute condition to every section fiber. -/

/-- A natural transformation preserves directed affine limits over its base if
every fiber functor preserves directed affine limits over the corresponding
scheme. -/
def IsLimitPreserving {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G) : Prop :=
  ∀ (T : Over S) (y : G.obj (op T)),
    PreservesDirectedAffineLimits T.left (fiberFunctor a y)

/-- The relative limit-preservation condition unfolds to its fiberwise form. -/
theorem isLimitPreserving_iff {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G) :
    IsLimitPreserving a ↔
      ∀ (T : Over S) (y : G.obj (op T)),
        PreservesDirectedAffineLimits T.left (fiberFunctor a y) := sorry

/-- A relatively limit-preserving transformation preserves directed affine
limits on each fiber functor. -/
theorem IsLimitPreserving.preserves {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type v} {a : F ⟶ G} (ha : IsLimitPreserving a)
    (T : Over S) (y : G.obj (op T)) :
    PreservesDirectedAffineLimits T.left (fiberFunctor a y) := sorry

namespace IsLimitPreserving

/-- The composite of relatively limit-preserving transformations is relatively
limit preserving. -/
theorem comp {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type v} {a : F ⟶ G} {b : G ⟶ H}
    (ha : IsLimitPreserving a) (hb : IsLimitPreserving b) :
    IsLimitPreserving (a ≫ b) := sorry

end IsLimitPreserving

end Scheme.Over

namespace Scheme

/-- A set-valued presheaf on schemes preserves directed inverse limits of
affine schemes. -/
def PreservesDirectedAffineLimits (F : Scheme.{u}ᵒᵖ ⥤ Type v) : Prop :=
  ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D),
      IsLimit c →
      (∀ i : I, IsAffine (D.obj i)) →
      IsAffine c.pt →
      Nonempty (IsColimit (F.mapCocone c.op))

/-- The directed-affine-limit condition unfolds to its diagrammatic form. -/
theorem preservesDirectedAffineLimits_iff (F : Scheme.{u}ᵒᵖ ⥤ Type v) :
    PreservesDirectedAffineLimits F ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D),
          IsLimit c →
          (∀ i : I, IsAffine (D.obj i)) →
          IsAffine c.pt →
          Nonempty (IsColimit (F.mapCocone c.op)) := sorry

/-- Absolute directed-affine-limit preservation implies the corresponding
condition after restriction to schemes over any base. -/
theorem PreservesDirectedAffineLimits.over {F : Scheme.{u}ᵒᵖ ⥤ Type v}
    (hF : PreservesDirectedAffineLimits F) (S : Scheme.{u}) :
    Over.PreservesDirectedAffineLimits S
      ((CategoryTheory.Over.forget S).op ⋙ F) := sorry

end Scheme

end AlgebraicGeometry
