/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.FiniteType

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
/- Lemma 37.30.1: if the generic fibre of a finite-type morphism to an irreducible
scheme has dimension `n`, then every fibre over some nonempty open has dimension `n`. -/
@[stacks 05F7] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.exists_open_topologicalKrullDim_fiber_eq :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y] {n : ℕ},
      topologicalKrullDim (f.fiber (genericPoint Y)) = (n : WithBot ℕ∞) →
        ∃ V : Y.Opens, Nonempty V ∧ ∀ y : Y, y ∈ V →
          topologicalKrullDim (f.fiber y) = (n : WithBot ℕ∞))

end Hom
end Scheme
end AlgebraicGeometry
