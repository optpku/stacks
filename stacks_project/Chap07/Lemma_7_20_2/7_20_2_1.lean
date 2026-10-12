/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Family.OverlapCofork
import StacksCheckRecall

/-!
# Lemma 7.20.2.1

The fixed-target-family overlap cofork is owned by ReasLib. This source file retains only the
literal presheaf-pullback presentation used by the Chapter 7 argument.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.FormalCoproduct

universe w v u v' u'

variable {D : Type u} [Category.{v} D] {V : D}
variable {C : Type u'} [Category.{v'} C]
variable (u : C ⥤ D) (𝒰 : FormalCoproduct.{w} (CategoryTheory.Over V))
variable [𝒰.toPresieve.HasPairwisePullbacks]

/- Lemma 7.20.2 (00XK), overlap presentation: for a fixed-target family `𝒰` with pairwise
pullbacks, the two maps from the coproduct of its pairwise-overlap representables to the coproduct
of its member representables agree after augmentation to the representable presheaf of the fixed
target. Restricting those presheaves along `u` gives the displayed cofork
`∐ u^p h_{V_i ×_V V_j} ⇉ ∐ u^p h_{V_i} ⟶ u^p h_V`. -/
@[stacks 00XK] #check
  (CategoryTheory.Limits.FormalCoproduct.overlapFamily 𝒰 :
    FormalCoproduct.{w} (CategoryTheory.Over V))

#check (CategoryTheory.Limits.FormalCoproduct.overlapCofork 𝒰 :
  Cofork (toPresheaf.map ((forgetOver V).map (overlapFst 𝒰)))
    (toPresheaf.map ((forgetOver V).map (overlapSnd 𝒰))))

#check (CategoryTheory.Limits.FormalCoproduct.whiskerLeftOverlapCofork u 𝒰 :
  Cofork (u.op.whiskerLeft (toPresheaf.map ((forgetOver V).map (overlapFst 𝒰))))
    (u.op.whiskerLeft (toPresheaf.map ((forgetOver V).map (overlapSnd 𝒰)))))
