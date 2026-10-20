/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.LocalRing
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Definition 41.11.4 (1): for a locally finite-type morphism to a locally Noetherian
scheme, étaleness at a point is equivalent to essential étaleness of the induced map on
local rings. -/
@[stacks 0259] #check
  (AlgebraicGeometry.Scheme.Hom.etaleAt_iff_stalkMap :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
      (x : X), f.EtaleAt x ↔ (f.stalkMap x).hom.EssEtale)

/- Definition 41.11.4 (2): a scheme morphism is étale exactly when it is étale at every
point of its source. -/
@[stacks 0259] #check
  (AlgebraicGeometry.Scheme.Hom.etale_iff_forall_etaleAt :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Etale f ↔ ∀ x : X, f.EtaleAt x)

end AlgebraicGeometry.Scheme.Hom
