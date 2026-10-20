/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyOpen.QuasiFinite

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.74.2: a locally quasi-finite morphism to a geometrically unibranch,
locally Noetherian scheme is universally open if every irreducible component of
the source dominates an irreducible component of the target. -/
@[stacks 0F32] #check
  (AlgebraicGeometry.Scheme.Hom.universallyOpen_of_dominantComponents :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
      [LocallyQuasiFinite f] [IsLocallyNoetherian Y],
      Y.isGeometricallyUnibranch →
        (∀ C : irreducibleComponents X, ∃ D : irreducibleComponents Y,
          closure (Set.image f.base (C : Set X)) = (D : Set Y)) →
        UniversallyOpen f)

end AlgebraicGeometry.Scheme.Hom
