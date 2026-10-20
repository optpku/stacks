/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.ConnectedComponents

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace FiniteType

/- Lemma 37.28.1: over some nonempty open subset of an irreducible base, the fibres of a
finite-type morphism have at least as many connected components as the generic fibre. -/
@[stacks 055D] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.exists_open_le_natCard_connectedComponents :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y] {n : ℕ},
      Nat.card (ConnectedComponents (f.fiber (genericPoint Y))) = n →
        ∃ V : Y.Opens, Nonempty V ∧ ∀ y : Y, y ∈ V →
          n ≤ Nat.card (ConnectedComponents (f.fiber y)))

end FiniteType
end Hom
end Scheme
end AlgebraicGeometry
