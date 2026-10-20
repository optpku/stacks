/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Colimit

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/- 63.4.0.2: The finite-support quotient is the colimit of the groups of
sections supported on locally closed subschemes finite over the base. -/
@[stacks 0F6M] #check
  (AlgebraicGeometry.Scheme.Etale.FiniteSupportColimit.groupIsoColimit :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale),
      FiniteSupportColimit.group f F V ≅ colimit (FiniteSupportColimit.diagram f F V))

end AlgebraicGeometry.Scheme.Etale

end
