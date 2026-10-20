/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Cap.OpenRestriction

/-!
# Open restriction of the fibre-cycle action on cycles

The fibre-cycle action commutes with restriction to compatible open subschemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

variable {S X Y : Scheme.{u}} [UniversallyCatenary S]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (r : ℕ) (e : ℤ)

/- Lemma 62.11.2: If `U ⊆ X` and `V ⊆ Y` are open and `f(U) ⊆ V`, then
`(α ∩ β)|_U` equals `α|_U ∩ β|_V`. -/
@[stacks 0H67] #check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.cap_openPullback p f δ (r := (r : ℤ)) (e := e) :
  ∀ (α : CyclesOnFibers f (r : ℤ))
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V),
    CycleGroup.toAlgebraicCycle
        ((U.ι ≫ f ≫ p).relativeDimensionFunction δ) ((r : ℤ) + e)
        (CycleGroup.Localization.openPullback (f ≫ p) δ U ((r : ℤ) + e)
          (cap p f δ α β)) =
      CycleGroup.toAlgebraicCycle
        ((f.resLE V U hUV ≫ V.ι ≫ p).relativeDimensionFunction δ) ((r : ℤ) + e)
        (cap (V.ι ≫ p) (f.resLE V U hUV) δ
          (restrict α U V hUV)
          (CycleGroup.Localization.openPullback p δ V e β)))

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.cap_openPullback_apply p f δ (r := (r : ℤ)) (e := e) :
  ∀ (α : CyclesOnFibers f (r : ℤ))
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (u : U.toScheme),
    CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ) ((r : ℤ) + e)
        (cap p f δ α β) (U.ι u) =
      CycleGroup.toAlgebraicCycle
        ((f.resLE V U hUV ≫ V.ι ≫ p).relativeDimensionFunction δ) ((r : ℤ) + e)
        (cap (V.ι ≫ p) (f.resLE V U hUV) δ
          (restrict α U V hUV)
          (CycleGroup.Localization.openPullback p δ V e β)) u)

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
