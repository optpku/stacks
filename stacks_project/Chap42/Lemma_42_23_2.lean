/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedK0.Equivalence

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.Modules
namespace GradedK0

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)

/- Lemma 42.23.2: Degree-`k` cycles are additively equivalent to the Grothendieck group of
coherent sheaves supported in relative dimension at most `k`, modulo those supported in
relative dimension at most `k - 1`. -/
@[stacks 02S9] #check
  (AlgebraicGeometry.Scheme.Modules.GradedK0.equiv f δ k :
    AlgebraicGeometry.CycleGroup X (f.relativeDimensionFunction δ) k ≃+
      AlgebraicGeometry.Scheme.Modules.GradedK0 f δ k)

end GradedK0
end Scheme.Modules
end AlgebraicGeometry
