/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree.RelativeDimension
import StacksCheckRecall

/-!
# Finite locally free morphisms of algebraic spaces and cycles

In Situation 82.2.1, a finite locally free morphism of degree `d` between good
algebraic spaces over `B` is proper and flat of relative dimension `0`, and
push-pull of `k`-cycles is multiplication by `d`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

section

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteLocallyFree f]

/- A finite locally free morphism of algebraic spaces is proper. -/
#check (inferInstance : Proper f)

/- A finite locally free morphism of algebraic spaces is flat. -/
#check (inferInstance : Flat f)

end

/- Lemma 82.11.2 (1): In Situation 82.2.1 let `X`, `Y / B` be good. Let
`f : X ⟶ Y` be a finite locally free morphism of degree `d`. Then `f` is of
relative dimension `0`. -/
@[stacks 0EPE] #check
  (AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree.instRelativeDimension_zero :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      (f : X ⟶ Y) [FiniteLocallyFree f], RelativeDimension f 0)

/- Lemma 82.11.2 (2): In Situation 82.2.1 let `X`, `Y / B` be good. Let
`f : X ⟶ Y` be a finite locally free morphism of degree `d`. Then
`f_* (f^* α) = d • α` for every `α ∈ Z_k(Y)`. -/
@[stacks 0EPE] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforward_flatPullback_nsmul :
    ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
      (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (f : X ⟶ Y) (d : ℕ) [FiniteLocallyFreeOfRank f d]
      (hf : f ≫ pY = pX) (k : ℤ) {α : Function.locallyFinsupp (Points Y) ℤ},
      α ∈ Hom.cycleGroup pY δ k →
        Hom.properPushforwardCycle pX pY δ f hf
            (Hom.flatPullback pY pX δ f 0 hf k α) = d • α)
