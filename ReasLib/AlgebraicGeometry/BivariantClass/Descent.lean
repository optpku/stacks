/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.TrivialRestriction
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveLineFamily

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- Cycle-level cap maps indexed by displayed cartesian base-change squares. -/
abbrev CycleCapFamily
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) :=
  ∀ {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left],
    IsPullback i.left f'.left f.left g.left → ∀ k : ℤ,
      CycleGroup Y'.left (Y'.hom.relativeDimensionFunction delta) k →+
        RelativeChow delta X' (k - p)

/-- Compatibility of cycle-level cap maps with effective-Cartier Gysin pullback when the
restricted invertible module is trivial. -/
def CompatibleWithTrivialCartierGysin
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {p : ℤ} (cap : CycleCapFamily delta f p) : Prop :=
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
      (k : ℤ) (alpha : CycleGroup Y'.left (Y'.hom.relativeDimensionFunction delta) k),
      HEq
        (cap (j ≫ i) f'' (h ≫ g) (inner.paste_horiz outer) (k - 1)
          (Scheme.Modules.trivialGysin Y'.hom delta ℒY sY htriv (k - 1)
            (CycleGroup.reindex (Y'.hom.relativeDimensionFunction delta)
              (Int.sub_add_cancel k 1).symm alpha)))
        (ChowGroup.gysin delta X' ℒX sX (k - p) (cap i f' g outer k alpha))

/-- A cycle-level cap family compatible with trivial-restriction effective-Cartier Gysin
pullback kills rational-equivalence boundaries. -/
theorem boundaries_le_ker
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {p : ℤ} (cap : CycleCapFamily delta f p)
    (hcap : CompatibleWithTrivialCartierGysin delta cap)
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (k : ℤ) :
    @RationalEquivalence.boundaries Y'.left
        (LocallyOfFiniteType.isLocallyNoetherian Y'.hom)
        (Y'.hom.relativeDimensionFunction delta) inferInstance k ≤
      (cap i f' g square k).ker := sorry

/-- Cycle-level cap maps take rationally equivalent cycles to the same Chow class. -/
theorem eq_of_rationallyEquivalent
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {p : ℤ} (cap : CycleCapFamily delta f p)
    (hcap : CompatibleWithTrivialCartierGysin delta cap)
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (k : ℤ)
    (alpha beta : CycleGroup Y'.left (Y'.hom.relativeDimensionFunction delta) k)
    (h : @RationalEquivalence.RationallyEquivalent Y'.left
      (LocallyOfFiniteType.isLocallyNoetherian Y'.hom)
      (Y'.hom.relativeDimensionFunction delta) inferInstance k alpha beta) :
    cap i f' g square k alpha = cap i f' g square k beta := sorry

/-- Descend a cycle-level cap family compatible with trivial-restriction Gysin pullback to
the corresponding family of maps on Chow groups. -/
noncomputable def descend
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {p : ℤ} (cap : CycleCapFamily delta f p)
    (hcap : CompatibleWithTrivialCartierGysin delta cap) : CapFamily delta f p :=
  fun {_ Y'} _ _ i f' g _ square k ↦
    QuotientAddGroup.lift
      (@RationalEquivalence.boundaries Y'.left
        (LocallyOfFiniteType.isLocallyNoetherian Y'.hom)
        (Y'.hom.relativeDimensionFunction delta) inferInstance k)
      (cap i f' g square k)
      (boundaries_le_ker delta cap hcap i f' g square k)

/-- Evaluation of the descended cap family on a Chow class is evaluation of the original
cycle-level cap map on its representative. -/
theorem descend_chowClass
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {p : ℤ} (cap : CycleCapFamily delta f p)
    (hcap : CompatibleWithTrivialCartierGysin delta cap)
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (k : ℤ)
    (alpha : CycleGroup Y'.left (Y'.hom.relativeDimensionFunction delta) k) :
    descend delta cap hcap i f' g square k
        (@chowClass Y'.left (LocallyOfFiniteType.isLocallyNoetherian Y'.hom)
          (Y'.hom.relativeDimensionFunction delta) inferInstance k alpha) =
      cap i f' g square k alpha := sorry

end AlgebraicGeometry.BivariantClass
