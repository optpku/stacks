/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.FlatBaseChange.AssociatedCycle
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.AssociatedCycle
public import ReasLib.AlgebraicGeometry.CycleGroup.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Over.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Over.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Over.BaseChange

/-!
# Flat pullback and flat base change of cycles

This file records that dimension-shifted flat base change commutes with flat
pullback on cycle groups.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

/-- Dimension-shifted base change commutes with flat pullback on cycle groups. -/
theorem baseChangePullback_flatPullback
    {S S' : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ X) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) :
    (reindex (((Over.pullback g).obj Y).hom.relativeDimensionFunction δ')
        (by
          rw [add_assoc k (r : ℤ) c, add_comm (r : ℤ) c,
            ← add_assoc k c (r : ℤ)])).comp
          ((baseChangePullback g δ δ' c hcompat Y.hom (k + (r : ℤ))).comp
            (flatPullback δ Y X f r k)) =
      (flatPullback δ' ((Over.pullback g).obj Y) ((Over.pullback g).obj X)
          ((Over.pullback g).map f) r (k + c)).comp
        (baseChangePullback g δ δ' c hcompat X.hom k) := sorry

end AlgebraicGeometry.CycleGroup
