/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ChernFiltration

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ChernClass
open AlgebraicGeometry.AlgebraicSpace.OperationalChow
open scoped BigOperators

universe u

/- Lemma 82.30.4: In Situation 82.2.1 let `X / B` be good. Let `L i`,
`i = 1, …, r` be invertible `𝒪_X`-modules. Let `E` be a locally free
`𝒪_X`-module of rank `r` endowed with a filtration
`0 = E 0 ⊂ ⋯ ⊂ E r = E` such that `E i / E (i - 1) ≅ L i`. Then
`c(E) = ∏_{i = 1}^r (1 + c₁(L i))` in `A^*(X)`. -/
@[stacks 0ESA] #check
  (AlgebraicGeometry.AlgebraicSpace.ChernClass.total_eq_prod_of_invertible_filtration :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    (L : Fin r → X.Modules) [∀ i : Fin r, isInvertibleObject (L i)]
    (F : Fin (r + 1) → Subobject E)
    (hstep : ∀ i : Fin r, F i.castSucc ≤ F i.succ)
    (hzero : F 0 = ⊥) (htop : F (Fin.last r) = ⊤)
    (e : ∀ i : Fin r,
      cokernel (Subobject.ofLE (F i.castSucc) (F i.succ) (hstep i)) ≅ L i),
    (∑ i : Fin (r + 1), homogeneous δ f i.val (chernClass δ f E i.val)) =
      (List.ofFn fun i : Fin r ↦
        1 + homogeneous δ f 1 (chernClass δ f (L i) 1)).prod)
