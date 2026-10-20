/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.EpiMono
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.Relative

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

namespace BivariantClass

/-- The cartesian-square-indexed cap maps underlying a degree-`p` bivariant class for
`f : X ⟶ Y`. -/
abbrev CapFamily
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) :=
  ∀ {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left],
    IsPullback i.left f'.left f.left g.left → ∀ k : ℤ,
      RelativeChow delta Y' k →+ RelativeChow delta X' (k - p)

/-- Compatibility of cap maps with proper pushforward in a cartesian square. -/
def CompatibleWithProperPushforward
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {p : ℤ} (cap : CapFamily delta f p) : Prop :=
  ∀ {X' Y' X'' Y'' : Over S}
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    [LocallyOfFiniteType X''.hom] [LocallyOfFiniteType Y''.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (outer : IsPullback i.left f'.left f.left g.left)
    (j : X'' ⟶ X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ Y')
    (inner : IsPullback j.left f''.left f'.left h.left)
    [IsProper h.left] [IsProper j.left] (k : ℤ) (alpha : RelativeChow delta Y'' k),
    cap i f' g outer k (ChowGroup.map delta Y'' Y' h k alpha) =
      ChowGroup.map delta X'' X' j (k - p)
        (cap (j ≫ i) f'' (h ≫ g) (inner.paste_horiz outer) k alpha)

/-- Compatibility of cap maps with flat pullback of fixed relative dimension. -/
def CompatibleWithFlatPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {p : ℤ} (cap : CapFamily delta f p) : Prop :=
  ∀ {X' Y' X'' Y'' : Over S}
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    [LocallyOfFiniteType X''.hom] [LocallyOfFiniteType Y''.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (outer : IsPullback i.left f'.left f.left g.left)
    (j : X'' ⟶ X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ Y')
    (inner : IsPullback j.left f''.left f'.left h.left) (r : ℕ)
    [Flat h.left] [Flat j.left]
    [Scheme.Hom.RelativeDimension h.left r] [Scheme.Hom.RelativeDimension j.left r]
    (k : ℤ) (alpha : RelativeChow delta Y' k),
    HEq
      (cap (j ≫ i) f'' (h ≫ g) (inner.paste_horiz outer) (k + r)
        (ChowGroup.flatPullback delta Y'' Y' h r k alpha))
      (ChowGroup.flatPullback delta X'' X' j r (k - p) (cap i f' g outer k alpha))

/-- Compatibility of cap maps with Gysin pullback along a zero scheme and its cartesian
pullback. -/
def CompatibleWithCartierGysin
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {p : ℤ} (cap : CapFamily delta f p) : Prop :=
  ∀ {X' Y' : Over S}
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (outer : IsPullback i.left f'.left f.left g.left)
    (ℒY : Y'.left.Modules) [Scheme.Modules.Invertible ℒY] (sY : ℒY.sections),
    let ℒX := (Scheme.Modules.pullback f'.left).obj ℒY
    let sX := Scheme.Modules.sectionsPullback f'.left ℒY sY
    let j : Over.mk (Scheme.zeroSchemeι ℒX sX ≫ X'.hom) ⟶ X' :=
      Over.homMk (Scheme.zeroSchemeι ℒX sX)
    let h : Over.mk (Scheme.zeroSchemeι ℒY sY ≫ Y'.hom) ⟶ Y' :=
      Over.homMk (Scheme.zeroSchemeι ℒY sY)
    ∀ [hFiniteType : LocallyOfFiniteType h.left]
      (f'' : Over.mk (Scheme.zeroSchemeι ℒX sX ≫ X'.hom) ⟶
        Over.mk (Scheme.zeroSchemeι ℒY sY ≫ Y'.hom))
      (inner : IsPullback j.left f''.left f'.left h.left)
      (k : ℤ) (alpha : RelativeChow delta Y' k),
      HEq
        (cap (j ≫ i) f'' (h ≫ g) (inner.paste_horiz outer) (k - 1)
          (ChowGroup.gysin delta Y' ℒY sY k alpha))
        (ChowGroup.gysin delta X' ℒX sX (k - p) (cap i f' g outer k alpha))

end BivariantClass

/-- A degree-`p` bivariant Chow class consists of cartesian-square-indexed cap maps compatible
with proper pushforward, flat pullback, and effective-Cartier Gysin pullback. -/
structure BivariantClass
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) where
  cap : BivariantClass.CapFamily delta f p
  map_proper : BivariantClass.CompatibleWithProperPushforward delta cap
  pullback_flat : BivariantClass.CompatibleWithFlatPullback delta cap
  gysin_cartier : BivariantClass.CompatibleWithCartierGysin delta cap

namespace BivariantClass

/-- Two bivariant classes are equal when their cap families agree. -/
@[ext]
theorem ext
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {p : ℤ} {c d : BivariantClass delta f p}
    (h : (c.cap : CapFamily delta f p) = (d.cap : CapFamily delta f p)) : c = d := sorry

/-- Reindex a cap family along a cartesian base-change square. -/
def restrictCap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    {f : X ⟶ Y} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (p : ℤ) :
    CapFamily delta f p → CapFamily delta f' p :=
  fun c {_ _} _ _ j f'' h _ inner k ↦
    c (j ≫ i) f'' (h ≫ g) (inner.paste_horiz square) k

/-- Reindexing along a cartesian square preserves proper-pushforward compatibility. -/
theorem restrict_map_proper
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    {f : X ⟶ Y} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (p : ℤ)
    (c : BivariantClass delta f p) :
    CompatibleWithProperPushforward delta (restrictCap delta i f' g square p c.cap) := sorry

/-- Reindexing along a cartesian square preserves flat-pullback compatibility. -/
theorem restrict_pullback_flat
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    {f : X ⟶ Y} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (p : ℤ)
    (c : BivariantClass delta f p) :
    CompatibleWithFlatPullback delta (restrictCap delta i f' g square p c.cap) := sorry

/-- Reindexing along a cartesian square preserves effective-Cartier Gysin compatibility. -/
theorem restrict_gysin_cartier
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    {f : X ⟶ Y} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (p : ℤ)
    (c : BivariantClass delta f p) :
    CompatibleWithCartierGysin delta (restrictCap delta i f' g square p c.cap) := sorry

/-- Restrict a bivariant class along a locally finite-type cartesian base-change square. -/
def restrict
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    {f : X ⟶ Y} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (p : ℤ) :
    BivariantClass delta f p → BivariantClass delta f' p :=
  fun c ↦
    { cap := restrictCap delta i f' g square p c.cap
      map_proper := restrict_map_proper delta i f' g square p c
      pullback_flat := restrict_pullback_flat delta i f' g square p c
      gysin_cartier := restrict_gysin_cartier delta i f' g square p c }

/-- Evaluation of a restricted bivariant class is evaluation of the original class on the
pasted cartesian square. -/
theorem restrict_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' X'' Y'' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    [LocallyOfFiniteType X''.hom] [LocallyOfFiniteType Y''.hom]
    {f : X ⟶ Y} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (p : ℤ)
    (c : BivariantClass delta f p)
    (j : X'' ⟶ X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ Y') [LocallyOfFiniteType h.left]
    (inner : IsPullback j.left f''.left f'.left h.left) (k : ℤ)
    (alpha : RelativeChow delta Y'' k) :
    (restrict delta i f' g square p c).cap j f'' h inner k alpha =
      c.cap (j ≫ i) f'' (h ≫ g) (inner.paste_horiz square) k alpha := sorry

/-- Successive restrictions of bivariant classes equal restriction along the pasted
cartesian square. -/
theorem restrict_comp
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' X'' Y'' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    [LocallyOfFiniteType X''.hom] [LocallyOfFiniteType Y''.hom]
    {f : X ⟶ Y} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left)
    (j : X'' ⟶ X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ Y') [LocallyOfFiniteType h.left]
    (inner : IsPullback j.left f''.left f'.left h.left) (p : ℤ)
    (c : BivariantClass delta f p) :
    restrict delta j f'' h inner p (restrict delta i f' g square p c) =
      restrict delta (j ≫ i) f'' (h ≫ g) (inner.paste_horiz square) p c := sorry

/-- Restriction of a bivariant class along a closed immersion to its source. -/
def restrictToSource
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Z.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (p : ℤ) :
    BivariantClass delta i p → BivariantClass delta (𝟙 Z) p :=
  restrict delta (𝟙 Z) (𝟙 Z) i
    ((mono_iff_isPullback i.left).mp inferInstance) p

/-- Capping after restricting a bivariant class to the source of a closed immersion
equals capping after proper pushforward along that immersion. -/
theorem restrictToSource_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Z.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (p k : ℤ)
    (c : BivariantClass delta i p) (alpha : RelativeChow delta Z k) :
    (restrictToSource delta i p c).cap (𝟙 Z) (𝟙 Z) (𝟙 Z)
        IsPullback.of_id_snd k alpha =
      c.cap (𝟙 Z) i (𝟙 X) (IsPullback.id_horiz i.left) k
        (ChowGroup.map delta Z X i k alpha) := sorry

end BivariantClass

end AlgebraicGeometry
