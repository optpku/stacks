/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.Constructible
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.76.1: every integer level set of a weighting of a locally quasi-finite
morphism is locally constructible in the source. -/
@[stacks 0F3G]
#check (AlgebraicGeometry.Scheme.Hom.IsWeighting.levelSet_isLocallyConstructible :
  ∀ {X Y : Scheme.{u}} {f : X ⟶ Y}
      [LocallyOfFiniteType f] [LocallyQuasiFinite f] {w : X → ℤ},
    f.IsWeighting w → ∀ n : ℤ,
      Topology.IsLocallyConstructible {x : X | w x = n})

end AlgebraicGeometry.Scheme.Hom
