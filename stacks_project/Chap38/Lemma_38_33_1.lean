/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Separated.OpenCover
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

/- Lemma 38.33.1: let `f : X ⟶ S` be a morphism of schemes and let `U` and `V` be
open subschemes covering `X`. If the restrictions of `f` to `U` and `V` are separated and the
canonical morphism `U ⊓ V ⟶ U ×_S V` is a closed immersion, then `f` is separated. -/
@[stacks 0F3U] #check (AlgebraicGeometry.IsSeparated.of_sup_eq_top :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (U V : X.Opens)
      (hcover : U ⊔ V = ⊤) [AlgebraicGeometry.IsSeparated (U.ι ≫ f)]
      [AlgebraicGeometry.IsSeparated (V.ι ≫ f)]
      [AlgebraicGeometry.IsClosedImmersion
        (pullback.lift (X.homOfLE (inf_le_left : U ⊓ V ≤ U))
          (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) :
            (U ⊓ V).toScheme ⟶ pullback (U.ι ≫ f) (V.ι ≫ f))],
      AlgebraicGeometry.IsSeparated f)
