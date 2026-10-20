/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.ExactSequence

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped BigOperators

universe u

namespace AlgebraicGeometry.ChernClass.Theory

/-- The total Chern class of a finite locally free module with invertible successive
quotients is the product of `1` plus the first Chern classes of those quotients. -/
theorem total_eq_prod_of_invertible_filtration
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : Theory δ p) (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFree E]
    (L : Fin r → X.Modules) [∀ i : Fin r, Scheme.Modules.Invertible (L i)]
    (F : Fin (r + 1) → Subobject E)
    (hstep : ∀ i : Fin r, F i.castSucc ≤ F i.succ)
    (hzero : F 0 = ⊥) (htop : F (Fin.last r) = ⊤)
    (e : ∀ i : Fin r,
      cokernel (Subobject.ofLE (F i.castSucc) (F i.succ) (hstep i)) ≅ L i) :
    (∑ i : Fin (r + 1),
      ChernClass.homogeneous δ p (i : ℕ) (classes.component E i)) =
      (List.ofFn fun i : Fin r ↦
        1 + ChernClass.homogeneous δ p 1 (classes.component (L i) 1)).prod := sorry

end AlgebraicGeometry.ChernClass.Theory
