/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.ClosedImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S}
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
variable (i : Z ⟶ X) [IsClosedImmersion i]

/- Lemma 69.12.8: Let `S` be a scheme. Let `i : Z ⟶ X` be a closed immersion of
locally Noetherian algebraic spaces over `S`. Let `I ⊂ 𝒪_X` be the quasi-coherent
sheaf of ideals cutting out `Z`, namely `Hom.idealSheaf i`. The functor `i_*`
induces an equivalence from the category of coherent `𝒪_Z`-modules to the
category of coherent `𝒪_X`-modules annihilated by `I`. -/
@[stacks 08AM] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.ClosedImmersion.coherentPushforward_isEquivalence i :
    (AlgebraicGeometry.AlgebraicSpace.Modules.ClosedImmersion.coherentPushforward i).IsEquivalence)
