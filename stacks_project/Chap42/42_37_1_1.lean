/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClass

@[expose] public section

open CategoryTheory
open scoped BigOperators

universe u

namespace AlgebraicGeometry

/- 42.37.1.1: If `E` is finite locally free of rank `r` on the integral scheme `X`
of `δ`-dimension `n`, then on its represented projective bundle `π : P ⟶ X` there are
classes `c_j ∈ CH_(n-j)(X)`, normalized by the fundamental class in degree zero, for which
`∑ i, (-1) ^ i • (c₁(𝒪_P(1)) ^ i ∩ π ^* c_(r-i))` vanishes in `CH_(n-1)(P)`. -/
@[stacks 02U1] #check
  (AlgebraicGeometry.ChowGroup.ProjectiveBundle.exists_chernClasses :
    ∀ {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
      [IsIntegral X] (E : X.Modules) (r : ℕ)
      [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
      (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
      (n : ℤ) (hn : p.relativeDimensionFunction δ (genericPoint X) = n),
      ∃ c : (j : Fin (r + 1)) →
          @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
            (p.relativeDimensionFunction δ) inferInstance (n - (j : ℕ)),
        c 0 =
            @chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
              (p.relativeDimensionFunction δ) inferInstance (n - (0 : ℕ))
              (@CycleGroup.fundamental X (LocallyOfFiniteType.isLocallyNoetherian p)
                (p.relativeDimensionFunction δ) (n - (0 : ℕ))) ∧
          ∑ i : Fin (r + 1),
              (-1 : ℤ) ^ (i : ℕ) •
                ChowGroup.ProjectiveBundle.Formula.chernTerm
                  δ p E r π hπ n i.rev (c i.rev) =
            0)

end AlgebraicGeometry
