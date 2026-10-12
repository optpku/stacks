/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Exhaustive
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.Data.Int.Interval

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.DecreasingFiltration

/-- A finite decreasing filtration in an abelian category with injective graded pieces splits
as a finite biproduct of those pieces, with every stage corresponding to its upper tail
through isomorphisms compatible with the stage inclusion. -/
theorem exists_iso_gradedPieces {C : Type u} [Category.{v} C] [Abelian C]
    [HasFiniteBiproducts C] (I : C) (F : DecreasingFiltration I)
    (hfinite : IndexedFiltration.IsFinite F)
    (hinjective : ∀ p : ℤ, Injective (cokernel (F.succInclusion p))) :
    ∃ a b : ℤ, a ≤ b ∧
      ∃ e : I ≅ ⨁ (fun n : Set.Icc a b ↦ cokernel (F.succInclusion n.val)),
        ∀ p : ℤ,
          ∃ ep : (F.stage p : C) ≅
              ⨁ (fun n : {n : Set.Icc a b // p ≤ n.val} ↦ cokernel (F.succInclusion n.1.val)),
            (F.stage p).arrow ≫ e.hom = ep.hom ≫
              biproduct.fromSubtype (fun n : Set.Icc a b ↦ cokernel (F.succInclusion n.val))
                (fun n : Set.Icc a b ↦ p ≤ n.val) := sorry

end CategoryTheory.DecreasingFiltration
