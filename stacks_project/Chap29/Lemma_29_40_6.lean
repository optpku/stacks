/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective.Cover
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 29.40.6

For a morphism of schemes, local quasi-projectivity is equivalent to H-quasi-projectivity after
restriction to every member of some open cover of the target.
-/
@[stacks 01VZ] #check
  (AlgebraicGeometry.locallyQuasiProjective_iff_exists_openCover_hQuasiProjective :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.LocallyQuasiProjective f ↔
        ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ i : 𝒰.I₀,
          AlgebraicGeometry.HQuasiProjective (f ∣_ ((𝒰.f i).opensRange)))
