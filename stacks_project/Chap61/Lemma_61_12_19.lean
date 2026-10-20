/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Glueing
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 61.12.19: a sheaf on the big pro-étale site over a scheme is equivalently a compatible
system of sheaves on the small pro-étale sites of schemes over the base, whose transitions are
invertible along weakly étale morphisms. -/
@[stacks 098V] #check
  (AlgebraicGeometry.Scheme.ProEt.SmallGlueing.fromSheaf_isEquivalence :
    ∀ S : Scheme.{u}, Functor.IsEquivalence
      (AlgebraicGeometry.Scheme.ProEt.SmallGlueing.fromSheaf S))
