/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.OpenImmersion
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 51.8.9: for a universally catenary scheme `X`, an open subscheme `U`,
and a coherent module `ℱ` with `(S₁)` formal fibers at every boundary point,
the pushforward of `ℱ` is coherent exactly when every boundary point in the
closure of an associated point has stalk dimension at least two. -/
@[stacks 0AWB] #check
  (AlgebraicGeometry.Scheme.Modules.pushforward_obj_isCoherent_iff_two_le_pointClosure_stalk_of_formalFibers :
    ∀ {X : Scheme.{u}} [UniversallyCatenary X] (U : X.Opens)
      (ℱ : (U : Scheme).Modules) [ℱ.IsCoherent]
      (h_formal : ∀ z : X, z ∉ U →
        (FieldAlgebraProperty.serreConditionS 1).HoldsOnFormalFibers
          (X.presheaf.stalk z)),
    ((pushforward U.ι).obj ℱ).IsCoherent ↔
      ∀ x : U, x ∈ ℱ.associatedPoints →
        ∀ y : PointClosure.scheme (U.ι x),
          PointClosure.ι (U.ι x) y ∉ U →
            2 ≤ ringKrullDim
              ((PointClosure.scheme (U.ι x)).presheaf.stalk y))

end AlgebraicGeometry.Scheme.Modules
