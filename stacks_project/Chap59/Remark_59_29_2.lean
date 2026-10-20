/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Over
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Remark 59.29.2: Since `U` and `U'` are étale over `S`, every `S`-morphism
between them is étale; in particular, every morphism of étale neighborhoods is
étale. -/
@[stacks 03PP] #check
  (AlgebraicGeometry.etale_of_etale_over :
    ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y),
      Etale X.hom → Etale Y.hom → Etale f.left)
