/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation.Sheafification

/-!
# Sheafification of limit-preserving transformations

A limit-preserving transformation of set-valued functors on the big fppf site
of schemes over `S` remains limit preserving after fppf sheafification.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Over

/- Lemma 70.3.9: if a limit-preserving transformation of functors on the
big fppf site over `S` is sheafified, the resulting transformation remains
limit preserving. -/
@[stacks 049Q] #check
  (AlgebraicGeometry.Scheme.Over.IsLimitPreserving.sheafifyMap :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type (u + 1)} {a : F ⟶ G},
      IsLimitPreserving a →
        IsLimitPreserving ((Scheme.fppfTopology.over S).sheafifyMap a))

end AlgebraicGeometry.Scheme.Over
