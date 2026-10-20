/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Endomorphism
import StacksCheckRecall

@[expose] public section

universe u v w x

open DifferentialGradedBimodule

variable {R : Type u} [CommRing R]
variable {B : CochainDGAlgebra.{u, x} R}
variable (A : CochainDGAlgebra.{u, w} R)
variable (M : DifferentialGradedModule.{u, v} B)

/- Lemma 22.28.2 (0FQI): compatible left DG `A`-actions on a fixed right DG `B`-module `M`
are canonically equivalent to DGA maps `A ⟶ End_{DGMod(B)}(M)`. -/
@[stacks 0FQI] #check
  (LeftAction.equivEndomorphismDGAHom A M :
    LeftAction A M ≃ CochainDGAlgebra.Hom A M.endomorphismDGA)

#check @LeftAction.ofBimodule
#check @LeftAction.fromBimodule
