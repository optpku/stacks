/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import stacks_project.Chap62.Example_62_5_4_AssociatedCycle
public import stacks_project.Chap62.Lemma_62_11_1_Cap
import Mathlib.Tactic.CrossRefAttribute

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

/-- The `δ`-dimension of the closed subscheme `Z ⊔ W.comap f` of `X`, which
realizes the scheme-theoretic fibre product `Z ×_Y W ⊂ X`, is at most
`(r : ℤ) + e`. -/
theorem closedSubschemeDeltaDimension_sup_comap_le {S X Y : Scheme.{u}}
    [UniversallyCatenary S] (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r)
    (W : Y.IdealSheafData) (e : ℤ)
    (hW : p.closedSubschemeDeltaDimension δ W ≤ (e : EInt)) :
    (f ≫ p).closedSubschemeDeltaDimension δ (Z ⊔ W.comap f) ≤
      ((r : ℤ) + e : EInt) :=
  sorry

/-- Lemma 62.11.5: Let `(S, δ)` and `f : X ⟶ Y` be as in the fibre-cycle action
setup, and let `Z ⊂ X` be a closed subscheme of relative dimension `≤ r` over
`Y`. Set `α = [Z/X/Y]_r` as `closedSubschemeFiberCycleFamily f Z r hZ`. Let
`W ⊂ Y` be a closed subscheme of `δ`-dimension `≤ e`. Set `β = [W]_e` as
`p.closedSubschemeCycle δ W e hW`. If `Z` is flat over `Y`, then
`α ∩ β = [Z ×_Y W]_{r + e}`, where `Z ×_Y W ⊂ X` is the closed subscheme
`Z ⊔ W.comap f`. -/
@[stacks 0H6A]
theorem cap_closedSubschemeFiberCycleFamily {S X Y : Scheme.{u}}
    [UniversallyCatenary S] (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r)
    (W : Y.IdealSheafData) (e : ℤ)
    (hW : p.closedSubschemeDeltaDimension δ W ≤ (e : EInt))
    [Flat (Z.subschemeι ≫ f)] :
    cap p f δ (closedSubschemeFiberCycleFamily f Z r hZ)
        (p.closedSubschemeCycle δ W e hW) =
      (f ≫ p).closedSubschemeCycle δ (Z ⊔ W.comap f) ((r : ℤ) + e)
        (closedSubschemeDeltaDimension_sup_comap_le p f δ Z r hZ W e hW) :=
  sorry

/-- Evaluating `cap_closedSubschemeFiberCycleFamily` compares coefficients of
both sides at a point of `X`. -/
theorem cap_closedSubschemeFiberCycleFamily_apply {S X Y : Scheme.{u}}
    [UniversallyCatenary S] (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r)
    (W : Y.IdealSheafData) (e : ℤ)
    (hW : p.closedSubschemeDeltaDimension δ W ≤ (e : EInt))
    [Flat (Z.subschemeι ≫ f)] (x : X) :
    CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (cap p f δ (closedSubschemeFiberCycleFamily f Z r hZ)
          (p.closedSubschemeCycle δ W e hW)) x =
      CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        ((f ≫ p).closedSubschemeCycle δ (Z ⊔ W.comap f) ((r : ℤ) + e)
          (closedSubschemeDeltaDimension_sup_comap_le p f δ Z r hZ W e hW)) x :=
  sorry

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
