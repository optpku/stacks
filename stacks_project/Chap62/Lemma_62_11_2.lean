/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.Localization
public import stacks_project.Chap62.Lemma_62_11_1_Cap
public import stacks_project.Chap62.Lemma_62_11_2_Restrict
import Mathlib.Tactic.CrossRefAttribute

/-!
# Open restriction of the fibre-cycle action on cycles

This file records that forming `α ∩ β` commutes with restriction to compatible
open subschemes of the source and target.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/-- Lemma 62.11.2: If `U ⊂ X` and `V ⊂ Y` are open and `f(U) ⊂ V`, then
`(α ∩ β)|_U` is equal to `α|_U ∩ β|_V`. -/
@[stacks 0H67]
theorem cap_openPullback {S X Y : Scheme.{u}} [UniversallyCatenary S]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ] {r e : ℤ}
    (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
    [LocallyOfFiniteType (f.resLE V U hUV ≫ V.ι ≫ p)] :
    CycleGroup.toAlgebraicCycle
        ((U.ι ≫ f ≫ p).relativeDimensionFunction δ) (r + e)
        (CycleGroup.Localization.openPullback (f ≫ p) δ U (r + e)
          (cap p f δ α β)) =
      CycleGroup.toAlgebraicCycle
        ((f.resLE V U hUV ≫ V.ι ≫ p).relativeDimensionFunction δ) (r + e)
        (cap (V.ι ≫ p) (f.resLE V U hUV) δ
          (restrict α U V hUV)
          (CycleGroup.Localization.openPullback p δ V e β)) := sorry

/-- Evaluating `cap_openPullback` at a point `u` of `U` compares the coefficient
of `cap p f δ α β` at `U.ι u` with the coefficient of `cap` after restricting
`α` and `β`. -/
theorem cap_openPullback_apply {S X Y : Scheme.{u}} [UniversallyCatenary S]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ] {r e : ℤ}
    (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
    [LocallyOfFiniteType (f.resLE V U hUV ≫ V.ι ≫ p)] (u : U.toScheme) :
    CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ) (r + e)
        (cap p f δ α β) (U.ι u) =
      CycleGroup.toAlgebraicCycle
        ((f.resLE V U hUV ≫ V.ι ≫ p).relativeDimensionFunction δ) (r + e)
        (cap (V.ι ≫ p) (f.resLE V U hUV) δ
          (restrict α U V hUV)
          (CycleGroup.Localization.openPullback p δ V e β)) u := sorry

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
