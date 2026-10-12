/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap69.Lemma_69_12_8_ClosedImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules.ClosedImmersion

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
  (coherentPushforward_isEquivalence i : (coherentPushforward i).IsEquivalence)
