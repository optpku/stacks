/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Subobject.Lattice
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ChernInvertibleSequence

/-!
# Total Chern class of a filtration by invertible quotients

A finite locally free module with invertible successive quotients has total
operational Chern class equal to the product of one plus their first Chern classes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ChernClass
open AlgebraicGeometry.AlgebraicSpace.OperationalChow
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChernClass

/-- The total operational Chern class of a rank-`r` finite locally free module
with an exhaustive filtration by invertible successive quotients is the ordered
product of one plus the first Chern classes of those quotients. -/
theorem total_eq_prod_of_invertible_filtration
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    (L : Fin r → X.Modules) [∀ i : Fin r, isInvertibleObject (L i)]
    (F : Fin (r + 1) → Subobject E)
    (hstep : ∀ i : Fin r, F i.castSucc ≤ F i.succ)
    (hzero : F 0 = ⊥) (htop : F (Fin.last r) = ⊤)
    (e : ∀ i : Fin r,
      cokernel (Subobject.ofLE (F i.castSucc) (F i.succ) (hstep i)) ≅ L i) :
    (∑ i : Fin (r + 1), homogeneous δ f i.val (chernClass δ f E i.val)) =
      (List.ofFn fun i : Fin r ↦
        1 + homogeneous δ f 1 (chernClass δ f (L i) 1)).prod :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ChernClass
