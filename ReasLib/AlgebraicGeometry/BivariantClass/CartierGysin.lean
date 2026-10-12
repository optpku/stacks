/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction
import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.TensorSplitting.Unit

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- Compatibility of Chow-level cap maps with effective-Cartier Gysin pullback when the
restricted invertible module is trivial. -/
def CompatibleWithTrivialCartierGysinOnChow
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
    ∀ (htriv : RingedSpace.IsTrivial
        ((Scheme.Modules.pullback (Scheme.zeroSchemeι ℒY sY)).obj ℒY))
      [hFiniteType : LocallyOfFiniteType h.left]
      (f'' : Over.mk (Scheme.zeroSchemeι ℒX sX ≫ X'.hom) ⟶
        Over.mk (Scheme.zeroSchemeι ℒY sY ≫ Y'.hom))
      (inner : IsPullback j.left f''.left f'.left h.left)
      (k : ℤ) (alpha : RelativeChow delta Y' k),
      HEq
        (cap (j ≫ i) f'' (h ≫ g) (inner.paste_horiz outer) (k - 1)
          (ChowGroup.gysin delta Y' ℒY sY k alpha))
        (ChowGroup.gysin delta X' ℒX sX (k - p) (cap i f' g outer k alpha))

/-- The quantified Gysin equation characterizing Chow-level compatibility under the
trivial-restriction hypothesis. -/
theorem compatibleWithTrivialCartierGysinOnChow_iff
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {p : ℤ} (cap : CapFamily delta f p) :
    CompatibleWithTrivialCartierGysinOnChow delta cap ↔
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
        ∀ (htriv : RingedSpace.IsTrivial
            ((Scheme.Modules.pullback (Scheme.zeroSchemeι ℒY sY)).obj ℒY))
          [hFiniteType : LocallyOfFiniteType h.left]
          (f'' : Over.mk (Scheme.zeroSchemeι ℒX sX ≫ X'.hom) ⟶
            Over.mk (Scheme.zeroSchemeι ℒY sY ≫ Y'.hom))
          (inner : IsPullback j.left f''.left f'.left h.left)
          (k : ℤ) (alpha : RelativeChow delta Y' k),
          HEq
            (cap (j ≫ i) f'' (h ≫ g) (inner.paste_horiz outer) (k - 1)
              (ChowGroup.gysin delta Y' ℒY sY k alpha))
            (ChowGroup.gysin delta X' ℒX sX (k - p) (cap i f' g outer k alpha)) := sorry

/-- Flat-pullback compatibility promotes trivial-restriction Cartier compatibility to
full effective-Cartier Gysin compatibility. -/
theorem compatibleWithCartierGysin_of_trivial
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {p : ℤ} (cap : CapFamily delta f p)
    (pullbackFlat : CompatibleWithFlatPullback delta cap)
    (gysinTrivial : CompatibleWithTrivialCartierGysinOnChow delta cap) :
    CompatibleWithCartierGysin delta cap := sorry

/-- A Chow-level cap family satisfying proper-pushforward, flat-pullback, and
trivial-restriction Cartier-Gysin compatibility determines a bivariant class. -/
def ofTrivialCartierGysin
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} (f : X ⟶ Y)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (p : ℤ) (cap : CapFamily delta f p)
    (mapProper : CompatibleWithProperPushforward delta cap)
    (pullbackFlat : CompatibleWithFlatPullback delta cap)
    (gysinTrivial : CompatibleWithTrivialCartierGysinOnChow delta cap) :
    AlgebraicGeometry.BivariantClass delta f p :=
  { cap := cap
    map_proper := mapProper
    pullback_flat := pullbackFlat
    gysin_cartier := compatibleWithCartierGysin_of_trivial delta cap pullbackFlat gysinTrivial }

/-- The cap family of `ofTrivialCartierGysin` is the supplied Chow-level cap family. -/
theorem ofTrivialCartierGysin_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} (f : X ⟶ Y)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (p : ℤ) (cap : CapFamily delta f p)
    (mapProper : CompatibleWithProperPushforward delta cap)
    (pullbackFlat : CompatibleWithFlatPullback delta cap)
    (gysinTrivial : CompatibleWithTrivialCartierGysinOnChow delta cap) :
    (@AlgebraicGeometry.BivariantClass.cap S _ delta _ X Y _ _ f p
        (ofTrivialCartierGysin delta f p cap mapProper pullbackFlat gysinTrivial) :
      CapFamily delta f p) = (@cap : CapFamily delta f p) := sorry

end AlgebraicGeometry.BivariantClass
