module

public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Cospan

/-- The cap maps associated to the two cartesian pullbacks of a cospan
`X ⟶ Z ⟵ Y`. -/
abbrev CapFamily
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (l : X ⟶ Z) (r : Y ⟶ Z) (p : ℤ) :=
  ∀ {Z' X' Y' : Over S}
    [LocallyOfFiniteType Z'.hom] [LocallyOfFiniteType X'.hom]
    [LocallyOfFiniteType Y'.hom]
    (g : Z' ⟶ Z) [LocallyOfFiniteType g.left]
    (iX : X' ⟶ X) (qX : X' ⟶ Z'),
    IsPullback iX.left qX.left l.left g.left →
    ∀ (iY : Y' ⟶ Y) [LocallyOfFiniteType iY.left] (qY : Y' ⟶ Z'),
    IsPullback iY.left qY.left r.left g.left → ∀ k : ℤ,
      RelativeChow delta Y' k →+ RelativeChow delta X' (k - p)

/-- Compatibility of cospan cap maps with proper pushforward after a base change of
the middle scheme. -/
def CompatibleWithProperPushforward
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] {l : X ⟶ Z} {r : Y ⟶ Z} {p : ℤ}
    (cap : CapFamily delta l r p) : Prop :=
  ∀ {Z' X' Y' Z'' X'' Y'' : Over S}
    [LocallyOfFiniteType Z'.hom] [LocallyOfFiniteType X'.hom]
    [LocallyOfFiniteType Y'.hom] [LocallyOfFiniteType Z''.hom]
    [LocallyOfFiniteType X''.hom] [LocallyOfFiniteType Y''.hom]
    (g : Z' ⟶ Z) [LocallyOfFiniteType g.left]
    (iX : X' ⟶ X) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left l.left g.left)
    (iY : Y' ⟶ Y) [LocallyOfFiniteType iY.left] (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left r.left g.left)
    (h : Z'' ⟶ Z') (jX : X'' ⟶ X') (qX' : X'' ⟶ Z'')
    (innerX : IsPullback jX.left qX'.left qX.left h.left)
    (jY : Y'' ⟶ Y') (qY' : Y'' ⟶ Z'')
    (innerY : IsPullback jY.left qY'.left qY.left h.left)
    [IsProper h.left] [IsProper jX.left] [IsProper jY.left]
    (k : ℤ) (alpha : RelativeChow delta Y'' k),
    cap g iX qX squareX iY qY squareY k
        (ChowGroup.map delta Y'' Y' jY k alpha) =
      ChowGroup.map delta X'' X' jX (k - p)
        (cap (h ≫ g) (jX ≫ iX) qX' (innerX.paste_horiz squareX)
          (jY ≫ iY) qY' (innerY.paste_horiz squareY) k alpha)

/-- Compatibility of cospan cap maps with flat pullback of a fixed relative
dimension after a base change of the middle scheme. -/
def CompatibleWithFlatPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] {l : X ⟶ Z} {r : Y ⟶ Z} {p : ℤ}
    (cap : CapFamily delta l r p) : Prop :=
  ∀ {Z' X' Y' Z'' X'' Y'' : Over S}
    [LocallyOfFiniteType Z'.hom] [LocallyOfFiniteType X'.hom]
    [LocallyOfFiniteType Y'.hom] [LocallyOfFiniteType Z''.hom]
    [LocallyOfFiniteType X''.hom] [LocallyOfFiniteType Y''.hom]
    (g : Z' ⟶ Z) [LocallyOfFiniteType g.left]
    (iX : X' ⟶ X) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left l.left g.left)
    (iY : Y' ⟶ Y) [LocallyOfFiniteType iY.left] (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left r.left g.left)
    (h : Z'' ⟶ Z') (jX : X'' ⟶ X') (qX' : X'' ⟶ Z'')
    (innerX : IsPullback jX.left qX'.left qX.left h.left)
    (jY : Y'' ⟶ Y') (qY' : Y'' ⟶ Z'')
    (innerY : IsPullback jY.left qY'.left qY.left h.left) (d : ℕ)
    [Flat h.left] [Flat jX.left] [Flat jY.left]
    [Scheme.Hom.RelativeDimension h.left d]
    [Scheme.Hom.RelativeDimension jX.left d]
    [Scheme.Hom.RelativeDimension jY.left d]
    (k : ℤ) (alpha : RelativeChow delta Y' k),
    HEq
      (cap (h ≫ g) (jX ≫ iX) qX' (innerX.paste_horiz squareX)
        (jY ≫ iY) qY' (innerY.paste_horiz squareY) (k + d)
        (ChowGroup.flatPullback delta Y'' Y' jY d k alpha))
      (ChowGroup.flatPullback delta X'' X' jX d (k - p)
        (cap g iX qX squareX iY qY squareY k alpha))

/-- Compatibility of cospan cap maps with the Gysin pullbacks of an effective
Cartier divisor on the varying middle scheme. -/
def CompatibleWithCartierGysin
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] {l : X ⟶ Z} {r : Y ⟶ Z} {p : ℤ}
    (cap : CapFamily delta l r p) : Prop :=
  ∀ {Z' X' Y' : Over S}
    [LocallyOfFiniteType Z'.hom] [LocallyOfFiniteType X'.hom]
    [LocallyOfFiniteType Y'.hom]
    (g : Z' ⟶ Z) [LocallyOfFiniteType g.left]
    (iX : X' ⟶ X) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left l.left g.left)
    (iY : Y' ⟶ Y) [LocallyOfFiniteType iY.left] (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left r.left g.left)
    (ℒZ : Z'.left.Modules) [Scheme.Modules.Invertible ℒZ] (sZ : ℒZ.sections),
    let ℒX := (Scheme.Modules.pullback qX.left).obj ℒZ
    let sX := Scheme.Modules.sectionsPullback qX.left ℒZ sZ
    let ℒY := (Scheme.Modules.pullback qY.left).obj ℒZ
    let sY := Scheme.Modules.sectionsPullback qY.left ℒZ sZ
    let jZ : Over.mk (Scheme.zeroSchemeι ℒZ sZ ≫ Z'.hom) ⟶ Z' :=
      Over.homMk (Scheme.zeroSchemeι ℒZ sZ)
    let jX : Over.mk (Scheme.zeroSchemeι ℒX sX ≫ X'.hom) ⟶ X' :=
      Over.homMk (Scheme.zeroSchemeι ℒX sX)
    let jY : Over.mk (Scheme.zeroSchemeι ℒY sY ≫ Y'.hom) ⟶ Y' :=
      Over.homMk (Scheme.zeroSchemeι ℒY sY)
    ∀ [jZFiniteType : LocallyOfFiniteType jZ.left]
      [jYFiniteType : LocallyOfFiniteType jY.left]
      (qX' : Over.mk (Scheme.zeroSchemeι ℒX sX ≫ X'.hom) ⟶
        Over.mk (Scheme.zeroSchemeι ℒZ sZ ≫ Z'.hom))
      (innerX : IsPullback jX.left qX'.left qX.left jZ.left)
      (qY' : Over.mk (Scheme.zeroSchemeι ℒY sY ≫ Y'.hom) ⟶
        Over.mk (Scheme.zeroSchemeι ℒZ sZ ≫ Z'.hom))
      (innerY : IsPullback jY.left qY'.left qY.left jZ.left)
      (k : ℤ) (alpha : RelativeChow delta Y' k),
      HEq
        (cap (jZ ≫ g) (jX ≫ iX) qX' (innerX.paste_horiz squareX)
          (jY ≫ iY) qY' (innerY.paste_horiz squareY) (k - 1)
          (ChowGroup.gysin delta Y' ℒY sY k alpha))
        (ChowGroup.gysin delta X' ℒX sX (k - p)
          (cap g iX qX squareX iY qY squareY k alpha))

end AlgebraicGeometry.BivariantClass.Cospan

namespace AlgebraicGeometry.BivariantClass

/-- A degree-`p` bivariant Chow operation on a cospan `X ⟶ Z ⟵ Y`, compatible
with proper pushforward, fixed-relative-dimension flat pullback, and
effective-Cartier Gysin pullback. -/
structure Cospan
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (l : X ⟶ Z) (r : Y ⟶ Z) (p : ℤ) where
  cap : Cospan.CapFamily delta l r p
  map_proper : Cospan.CompatibleWithProperPushforward delta cap
  pullback_flat : Cospan.CompatibleWithFlatPullback delta cap
  gysin_cartier : Cospan.CompatibleWithCartierGysin delta cap

namespace Cospan

/-- Two cospan bivariant classes are equal when all their cap maps agree. -/
@[ext]
theorem ext
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] {l : X ⟶ Z} {r : Y ⟶ Z} {p : ℤ}
    {c d : Cospan delta l r p}
    (h : (c.cap : CapFamily delta l r p) = (d.cap : CapFamily delta l r p)) : c = d := sorry

/-- The equality needed to lift into an identity-leg pullback. -/
theorem ofMorphismLift_comm
    {S : Scheme.{u}} {X Y X' Z' : Over S} (f : X ⟶ Y) (g : Z' ⟶ Y)
    (iX : X' ⟶ X) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left f.left g.left) :
    (iX.left ≫ f.left) ≫ (𝟙 Y : Y ⟶ Y).left = qX.left ≫ g.left := sorry

/-- The comparison into an identity-leg pullback respects the maps to the base
scheme. -/
theorem ofMorphismMap_over
    {S : Scheme.{u}} {X Y X' Z' Y' : Over S} (f : X ⟶ Y) (g : Z' ⟶ Y)
    (iX : X' ⟶ X) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left f.left g.left)
    (iY : Y' ⟶ Y) (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left (𝟙 Y : Y ⟶ Y).left g.left) :
    squareY.lift (iX.left ≫ f.left) qX.left
        (ofMorphismLift_comm f g iX qX squareX) ≫ Y'.hom = X'.hom := sorry

/-- The comparison from the left pullback to a displayed pullback of the identity
right leg. -/
def ofMorphismMap
    {S : Scheme.{u}} {X Y X' Z' Y' : Over S} (f : X ⟶ Y) (g : Z' ⟶ Y)
    (iX : X' ⟶ X) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left f.left g.left)
    (iY : Y' ⟶ Y) (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left (𝟙 Y : Y ⟶ Y).left g.left) : X' ⟶ Y' :=
  Over.homMk
    (squareY.lift (iX.left ≫ f.left) qX.left (ofMorphismLift_comm f g iX qX squareX))
    (ofMorphismMap_over f g iX qX squareX iY qY squareY)

/-- The comparison forms the cartesian square required by the ordinary bivariant
cap family. -/
theorem ofMorphismMap_isPullback
    {S : Scheme.{u}} {X Y X' Z' Y' : Over S} (f : X ⟶ Y) (g : Z' ⟶ Y)
    (iX : X' ⟶ X) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left f.left g.left)
    (iY : Y' ⟶ Y) (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left (𝟙 Y : Y ⟶ Y).left g.left) :
    IsPullback iX.left (ofMorphismMap f g iX qX squareX iY qY squareY).left
      f.left iY.left := sorry

/-- The cap family obtained from an ordinary bivariant class by giving it an identity
right leg. -/
def ofMorphismCap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p) :
    CapFamily delta f (𝟙 Y) p :=
  fun {_ _ _} _ _ _ g _ iX qX squareX iY _ qY squareY k ↦
    c.cap iX (ofMorphismMap f g iX qX squareX iY qY squareY) iY
      (ofMorphismMap_isPullback f g iX qX squareX iY qY squareY) k

/-- The identity-leg cap family preserves proper-pushforward compatibility. -/
theorem ofMorphismCap_mapProper
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p) :
    CompatibleWithProperPushforward delta (ofMorphismCap delta f p c) := sorry

/-- The identity-leg cap family preserves flat-pullback compatibility. -/
theorem ofMorphismCap_pullbackFlat
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p) :
    CompatibleWithFlatPullback delta (ofMorphismCap delta f p c) := sorry

/-- The identity-leg cap family preserves effective-Cartier Gysin compatibility. -/
theorem ofMorphismCap_gysinCartier
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p) :
    CompatibleWithCartierGysin delta (ofMorphismCap delta f p c) := sorry

/-- Regard an ordinary bivariant class as a cospan class whose right leg is the
identity. -/
def ofMorphism
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p) : Cospan delta f (𝟙 Y) p where
  cap := ofMorphismCap delta f p c
  map_proper := ofMorphismCap_mapProper delta f p c
  pullback_flat := ofMorphismCap_pullbackFlat delta f p c
  gysin_cartier := ofMorphismCap_gysinCartier delta f p c

/-- Evaluation of `ofMorphism` is evaluation of the original class along the canonical
comparison to the displayed identity pullback. -/
theorem ofMorphism_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z' X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z'.hom] [LocallyOfFiniteType X'.hom]
    [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p)
    (g : Z' ⟶ Y) [LocallyOfFiniteType g.left]
    (iX : X' ⟶ X) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left f.left g.left)
    (iY : Y' ⟶ Y) [LocallyOfFiniteType iY.left] (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left (𝟙 Y : Y ⟶ Y).left g.left) (k : ℤ) :
    (ofMorphism delta f p c).cap g iX qX squareX iY qY squareY k =
      c.cap iX (ofMorphismMap f g iX qX squareX iY qY squareY) iY
        (ofMorphismMap_isPullback f g iX qX squareX iY qY squareY) k := sorry

end AlgebraicGeometry.BivariantClass.Cospan
