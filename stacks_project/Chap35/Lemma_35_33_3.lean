/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.RepresentedBy
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget

open Scheme.Germ

/- Lemma 35.33.3: an étale-local-on-source-and-target property holds for a scheme
morphism exactly when its associated property holds for every induced morphism of germs. -/
@[stacks 04R7] #check
  (AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget.iff_forall_germ :
    ∀ (P : MorphismProperty Scheme.{u}) [IsEtaleLocalAtSourceAndTarget P]
      {X Y : Scheme.{u}} (f : X ⟶ Y),
      P f ↔ ∀ x : X, MorphismProperty.representedBy P
        (Hom.ofGlobal f rfl : Scheme.Germ.of X x ⟶ Scheme.Germ.of Y (f x)))

end AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
