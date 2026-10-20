/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Sheaf

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

/- Lemma 99.8.2: in Situation 99.8.1 the functor `Quot_{F/X/B}` on `(Sch/B)ᵒᵖ`
satisfies the sheaf property for the fpqc topology. -/
@[stacks 09TT] #check (AlgebraicGeometry.AlgebraicSpace.Quot.quot_isSheaf_fpqc :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent],
    Presheaf.IsSheaf (SchemeOver.fpqcTopology B) (AlgebraicGeometry.AlgebraicSpace.Quot.quot f F))
