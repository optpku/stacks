/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Noetherian.Topology
public import ReasLib.Topology.Specialization.Dimension.Catenary
import StacksCheckRecall

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (S : Scheme.{u}) [IsLocallyNoetherian S]

/- Lemma 28.11.3: A locally Noetherian scheme is catenary if and only if every point has a
Zariski-open neighbourhood whose induced topology admits an integer-valued dimension function. -/
@[stacks 02IY] #check
  (TopologicalSpace.catenarySpace_iff_locally_exists_dimensionFunction (X := S) :
    CatenarySpace S ↔
      ∀ x : S, ∃ U : S.Opens, x ∈ U ∧ ∃ δ : U → ℤ, IsDimensionFunction δ)

end AlgebraicGeometry
