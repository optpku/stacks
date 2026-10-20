/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Factorization
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 29.43.12: A quasi-projective morphism over a quasi-compact and quasi-separated scheme
factors as an open immersion followed by a projective morphism. -/
@[stacks 07RM] #check
  (AlgebraicGeometry.QuasiProjective.exists_factor_openImmersion_projective :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} [CompactSpace S] [QuasiSeparatedSpace S],
      QuasiProjective f →
        ∃ (X' : Scheme.{u}) (i : X ⟶ X') (g : X' ⟶ S)
          (_ : IsOpenImmersion i) (_ : Projective g),
            i ≫ g = f)
