/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Dimension
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry

/- Lemma 35.21.3: an étale morphism preserves the Krull dimension of the local ring at
every source point and its image. -/
@[stacks 04N8] #check
  (AlgebraicGeometry.Etale.ringKrullDim_stalk_eq :
    ∀ {U V : Scheme.{u}} (f : U ⟶ V) [Etale f] (u : U),
      ringKrullDim (U.presheaf.stalk u) = ringKrullDim (V.presheaf.stalk (f u)))

end AlgebraicGeometry
