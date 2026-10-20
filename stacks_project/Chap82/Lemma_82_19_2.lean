module

public import stacks_project.Chap82.Definition_82_18_1_ChernCap
public import stacks_project.Chap82.Lemma_82_11_1_Pullback

/-!
# Flat pullback of first-Chern intersection on algebraic spaces

In Situation 82.2.1, flat pullback of relative dimension `r` commutes with
intersecting a cycle by the first Chern class of an invertible sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Pullback of an invertible module along a morphism of algebraic spaces remains
invertible. -/
instance instIsInvertibleObject_modulesPullback {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (L : Y.Modules)
    [isInvertibleObject L] :
    isInvertibleObject ((Modules.pullback f).obj L) :=
  Modules.isInvertibleObject_pullback f L

/-- Lemma 82.19.2: In Situation 82.2.1 let `X`, `Y / B` be good. Let
`f : X ⟶ Y` be a flat morphism of relative dimension `r`. Let `L` be an
invertible sheaf on `Y`. Let `α` be a `(k + 1)`-cycle on `Y`. Then
`f^*(c1(L) ∩ α) = c1((Modules.pullback f).obj L) ∩ f^* α` in
`chowGroup pX δ (k + (r : ℤ))`. This is the source equality in
`CH_{k+r-1}(X)` for a `k`-cycle, after the Chern-cap indexing
`k_src = k + 1`. The left-hand side is the Chow class of the cycle-level
flat pullback of a first-Chern cycle representative; the right-hand side
caps the pulled-back invertible sheaf against the cycle-level flat
pullback of `α`. -/
@[stacks 0EQR]
theorem flatPullback_firstChernClassCap {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (L : Y.Modules) [isInvertibleObject L]
    (k : ℤ) (α : cycleGroup pY δ (k + 1)) :
    chowMk pX δ (k + (r : ℤ))
        (cycleFlatPullback pY pX δ f r hf k
          ⟨firstChernCycle pY δ L k α, firstChernCycle_mem pY δ L k α⟩) =
      firstChernClassCap pX δ ((Modules.pullback f).obj L) (k + (r : ℤ))
        (add_right_comm k 1 (r : ℤ) ▸
          cycleFlatPullback pY pX δ f r hf (k + 1) α) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
