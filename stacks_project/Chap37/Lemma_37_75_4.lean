/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.75.4: restricting a weighting of a locally quasi-finite morphism to an
open subscheme of its source again gives a weighting. -/
@[stacks 0GK8] #check
  (AlgebraicGeometry.Scheme.Hom.IsWeighting.restrict :
    ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} [LocallyQuasiFinite f] {w : X → ℤ},
      f.IsWeighting w → ∀ U : X.Opens, (U.ι ≫ f).IsWeighting (fun x : U ↦ w x))

end AlgebraicGeometry.Scheme.Hom
