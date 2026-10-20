/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cap action and composition of families of cycles on fibres
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

/-- Composition of families of cycles on fibres acts associatively with the
cap action on cycles. -/
@[stacks 0H6P]
theorem cap_comp {S X Y Z : Scheme.{u}} [UniversallyCatenary S]
    (p : Z ⟶ S) (g : Y ⟶ Z) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType g] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] {r s e : ℕ}
    (α : CyclesOnFibers f (r : ℤ)) (β : CyclesOnFibers g (s : ℤ))
    (γ : CycleGroup Z (p.relativeDimensionFunction δ) (e : ℤ)) :
    CycleGroup.toAlgebraicCycle (((f ≫ g) ≫ p).relativeDimensionFunction δ)
        ((r : ℤ) + (s : ℤ) + (e : ℤ)) (cap p (f ≫ g) δ (comp α β) γ) =
      CycleGroup.toAlgebraicCycle ((f ≫ g ≫ p).relativeDimensionFunction δ)
        ((r : ℤ) + ((s : ℤ) + (e : ℤ)))
        (cap (g ≫ p) f δ α (cap p g δ β γ)) := sorry

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
