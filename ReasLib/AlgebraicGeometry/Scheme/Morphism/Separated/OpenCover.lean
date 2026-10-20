/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.IsSeparated

/-- If two open subschemes cover a scheme, their maps to the target are separated, and the
canonical map from their intersection to their fiber product is a closed immersion, then the
scheme's map to the target is separated. -/
theorem of_sup_eq_top {X S : Scheme.{u}} (f : X ⟶ S) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) [IsSeparated (U.ι ≫ f)] [IsSeparated (V.ι ≫ f)]
    [IsClosedImmersion
      (pullback.lift (X.homOfLE (inf_le_left : U ⊓ V ≤ U))
        (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) :
          (U ⊓ V).toScheme ⟶ pullback (U.ι ≫ f) (V.ι ≫ f))] :
    IsSeparated f := sorry

end AlgebraicGeometry.IsSeparated
