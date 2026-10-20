/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.75.3: an integer-valued weighting pulls back along an arbitrary base
change of a locally quasi-finite scheme morphism. -/
@[stacks 0F3B]
#check (AlgebraicGeometry.Scheme.Hom.IsWeighting.baseChange :
  ∀ {X Y Y' : Scheme.{u}} {f : X ⟶ Y} [LocallyQuasiFinite f] {w : X → ℤ},
    f.IsWeighting w → ∀ g : Y' ⟶ Y,
      (pullback.snd f g).IsWeighting (fun x' ↦ w (pullback.fst f g x')))

end AlgebraicGeometry.Scheme.Hom
