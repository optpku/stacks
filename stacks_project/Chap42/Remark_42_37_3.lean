/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import stacks_project.Chap42.«42_37_3_1»

open CategoryTheory
open scoped BigOperators

universe u

namespace AlgebraicGeometry

/- Remark 42.37.3: The projective-bundle Chern relation can equivalently be written
as the unsigned vanishing relation using the dual tautological module `𝒪_P(-1)`,
although the tautological quotient module `𝒪_P(1)` is more convenient in practice. -/
@[stacks 02U3] #check
  (AlgebraicGeometry.ChowGroup.ProjectiveBundle.exists_chernClasses_dual_relation :
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
              ChowGroup.ProjectiveBundle.Formula.dualChernTerm
                δ p E r π hπ n i.rev (c i.rev) =
            0)

end AlgebraicGeometry
