/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap62.Lemma_62_11_1_Cap
public import stacks_project.Chap62.Example_62_5_2_AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Coherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated cycles of a cap product

This file records that the fibre-cycle action of the associated cycle family
of a coherent module flat over the base recovers the associated cycle of the
tensor with the pullback of a coherent module of bounded support dimension.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/-- Lemma 62.11.4: Let `(S, δ)` and `f : X ⟶ Y` be as in the fibre-cycle action
setup, and let `F` be a coherent `O_X`-module with `dim(Supp(F_y)) ≤ r` for all
`y ∈ Y`. Let `G` be a coherent `O_Y`-module with `dim_δ(Supp(G)) ≤ e`. Set
`α = [F/X/Y]_r` as `moduleFiberCycleFamily f F r hF` and
`β = [G]_e` as `Modules.relativeAssociatedCycle p δ G e`. If `F` is flat over
`Y`, then `α ∩ β = [F ⊗ (Modules.pullback f).obj G]_{r + e}`. -/
@[stacks 0H69]
theorem cap_moduleFiberCycleFamily {S X Y : Scheme.{u}} [UniversallyCatenary S]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (F : X.Modules) [F.IsCoherent] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r)
    (G : Y.Modules) [G.IsCoherent] (e : ℤ)
    (hG : ∀ y ∈ Modules.moduleSupport G, p.relativeDimensionFunction δ y ≤ e)
    (hflat : Modules.flatOver F f) :
    cap p f δ (moduleFiberCycleFamily f F r hF)
        (Modules.relativeAssociatedCycle p δ G e) =
      Modules.relativeAssociatedCycle (f ≫ p) δ
        (F ⊗ (Modules.pullback f).obj G) ((r : ℤ) + e) :=
  sorry

/-- Evaluating `cap_moduleFiberCycleFamily` compares coefficients of both sides
at a point of `X`. -/
theorem cap_moduleFiberCycleFamily_apply {S X Y : Scheme.{u}}
    [UniversallyCatenary S] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (F : X.Modules) [F.IsCoherent] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r)
    (G : Y.Modules) [G.IsCoherent] (e : ℤ)
    (hG : ∀ y ∈ Modules.moduleSupport G, p.relativeDimensionFunction δ y ≤ e)
    (hflat : Modules.flatOver F f) (x : X) :
    CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (cap p f δ (moduleFiberCycleFamily f F r hF)
          (Modules.relativeAssociatedCycle p δ G e)) x =
      CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (Modules.relativeAssociatedCycle (f ≫ p) δ
          (F ⊗ (Modules.pullback f).obj G) ((r : ℤ) + e)) x :=
  sorry

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
