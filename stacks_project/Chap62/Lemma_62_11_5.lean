module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.ClosedSubscheme
import StacksCheckRecall

/-!
# Associated cycles of a closed-subscheme cap product

This file records that the fibre-cycle action of the associated cycle family
of a closed subscheme flat over the base recovers the associated cycle of the
scheme-theoretic fibre product with a closed subscheme of bounded support
dimension.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/- The scheme-theoretic fibre product has the required dimension bound. -/
#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.closedSubschemeDeltaDimension_sup_comap_le :
  ∀ {S X Y : Scheme.{u}}
    [UniversallyCatenary S] (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r)
    (W : Y.IdealSheafData) (e : ℤ)
    (hW : p.closedSubschemeDeltaDimension δ W ≤ (e : EInt)),
    (f ≫ p).closedSubschemeDeltaDimension δ (Z ⊔ W.comap f) ≤
      ((r : ℤ) + e : EInt))

/- Lemma 62.11.5: Let `(S, δ)` and `f : X ⟶ Y` be as in the fibre-cycle action
setup, and let `Z ⊂ X` be a closed subscheme of relative dimension `≤ r` over
`Y`. Set `α = [Z/X/Y]_r` as `closedSubschemeFiberCycleFamily f Z r hZ`. Let
`W ⊂ Y` be a closed subscheme of `δ`-dimension `≤ e`. Set `β = [W]_e` as
`p.closedSubschemeCycle δ W e hW`. If `Z` is flat over `Y`, then
`α ∩ β = [Z ×_Y W]_{r + e}`, where `Z ×_Y W ⊂ X` is the closed subscheme
`Z ⊔ W.comap f`. -/
@[stacks 0H6A]
#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.cap_closedSubschemeFiberCycleFamily :
  ∀ {S X Y : Scheme.{u}}
    [UniversallyCatenary S] (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r)
    (W : Y.IdealSheafData) (e : ℤ)
    (hW : p.closedSubschemeDeltaDimension δ W ≤ (e : EInt))
    [Flat (Z.subschemeι ≫ f)],
    cap p f δ (closedSubschemeFiberCycleFamily f Z r hZ)
        (p.closedSubschemeCycle δ W e hW) =
      (f ≫ p).closedSubschemeCycle δ (Z ⊔ W.comap f) ((r : ℤ) + e)
        (closedSubschemeDeltaDimension_sup_comap_le p f δ Z r hZ W e hW))

/- Evaluating `cap_closedSubschemeFiberCycleFamily` compares coefficients of
both sides at a point of `X`. -/
#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.cap_closedSubschemeFiberCycleFamily_apply :
  ∀ {S X Y : Scheme.{u}}
    [UniversallyCatenary S] (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r)
    (W : Y.IdealSheafData) (e : ℤ)
    (hW : p.closedSubschemeDeltaDimension δ W ≤ (e : EInt))
    [Flat (Z.subschemeι ≫ f)] (x : X),
    CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (cap p f δ (closedSubschemeFiberCycleFamily f Z r hZ)
          (p.closedSubschemeCycle δ W e hW)) x =
      CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        ((f ≫ p).closedSubschemeCycle δ (Z ⊔ W.comap f) ((r : ℤ) + e)
          (closedSubschemeDeltaDimension_sup_comap_le p f δ Z r hZ W e hW)) x)

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
