/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.GenericSeparableDegree

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.75.8: a locally finite-type, locally quasi-finite morphism to a
geometrically unibranch, locally Noetherian scheme admits a nonnegative
weighting given pointwise by generic separable degrees on stalks. -/
@[stacks 0F3E] #check
  (AlgebraicGeometry.Scheme.Hom.exists_genericSepDegreeWeighting :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsLocallyNoetherian Y],
      Y.isGeometricallyUnibranch →
        ∃ w : X → ℕ, f.IsWeighting (fun x ↦ (w x : ℤ)) ∧
          ∀ x : X, RingHom.IsGenericSepDegree (f.stalkMap x).hom
            (LocallyOfFiniteType.stalkMap f x) (f.quasiFiniteAt x) (w x))

end AlgebraicGeometry.Scheme.Hom
