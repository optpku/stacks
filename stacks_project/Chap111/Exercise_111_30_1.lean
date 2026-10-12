/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.IntervalSplit.GradedPiece
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

/- Exercise 111.30.1: in an abelian category `C`, an object `I` with a finite
decreasing filtration `F` and injective graded pieces `cokernel (F.succInclusion p)`
is isomorphic to their biproduct over some finite interval `Set.Icc a b`.
For every `p`, the stage `F.stage p` corresponds to the tail indexed by `n ≥ p`,
with its inclusion commuting with the ambient isomorphism and the canonical
tail inclusion `biproduct.fromSubtype`. -/
@[stacks 0288] #check
  (CategoryTheory.DecreasingFiltration.exists_iso_gradedPieces :
    ∀ {C : Type u} [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]
      (I : C) (F : DecreasingFiltration I) (hfinite : IndexedFiltration.IsFinite F)
      (hinjective : ∀ p : ℤ, Injective (cokernel (F.succInclusion p))),
      ∃ a b : ℤ, a ≤ b ∧
        ∃ e : I ≅ ⨁ (fun n : Set.Icc a b ↦ cokernel (F.succInclusion n.val)),
          ∀ p : ℤ,
            ∃ ep : (F.stage p : C) ≅
                ⨁ (fun n : {n : Set.Icc a b // p ≤ n.val} ↦ cokernel (F.succInclusion n.1.val)),
              (F.stage p).arrow ≫ e.hom = ep.hom ≫
                biproduct.fromSubtype (fun n : Set.Icc a b ↦ cokernel (F.succInclusion n.val))
                  (fun n : Set.Icc a b ↦ p ≤ n.val))
