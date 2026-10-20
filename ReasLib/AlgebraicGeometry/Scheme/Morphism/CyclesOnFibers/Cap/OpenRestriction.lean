/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Cap
public import ReasLib.AlgebraicGeometry.CycleGroup.Localization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Restriction

/-!
# Open restriction of the fibre-cycle action on cycles

The fibre-cycle action commutes with restriction to compatible open subschemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/-- Restricting the fibre-cycle action to an open subscheme equals the action
of the restricted fibre-cycle family on the restricted base cycle. -/
theorem cap_openPullback {S X Y : Scheme.{u}} [UniversallyCatenary S]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] {r e : ℤ}
    (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V) :
    CycleGroup.toAlgebraicCycle
        ((U.ι ≫ f ≫ p).relativeDimensionFunction δ) (r + e)
        (CycleGroup.Localization.openPullback (f ≫ p) δ U (r + e)
          (cap p f δ α β)) =
      CycleGroup.toAlgebraicCycle
        ((f.resLE V U hUV ≫ V.ι ≫ p).relativeDimensionFunction δ) (r + e)
        (cap (V.ι ≫ p) (f.resLE V U hUV) δ
          (restrict α U V hUV)
          (CycleGroup.Localization.openPullback p δ V e β)) := sorry

/-- The coefficient of the fibre-cycle action at a point of an open subscheme
is the coefficient of the action of the restricted family on the restricted
base cycle. -/
theorem cap_openPullback_apply {S X Y : Scheme.{u}} [UniversallyCatenary S]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] {r e : ℤ}
    (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (u : U.toScheme) :
    CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ) (r + e)
        (cap p f δ α β) (U.ι u) =
      CycleGroup.toAlgebraicCycle
        ((f.resLE V U hUV ≫ V.ι ≫ p).relativeDimensionFunction δ) (r + e)
        (cap (V.ι ≫ p) (f.resLE V U hUV) δ
          (restrict α U V hUV)
          (CycleGroup.Localization.openPullback p δ V e β)) u := sorry

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
