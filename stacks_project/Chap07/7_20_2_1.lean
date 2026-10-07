module

public import ReasLib.CategoryTheory.Sites.Family.OverlapCofork
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SemiRepresentableFamily.Over

universe w v u v' u'

variable {D : Type u} [Category.{v} D] {V : D}
variable {C : Type u'} [Category.{v'} C]
variable (u : C ⥤ D) (𝒰 : SemiRepresentableFamily.Over.{w} V)
variable [𝒰.toPresieve.HasPairwisePullbacks]

/- 7.20.2.1: the displayed diagram
   ∐ u^p h_{V_j ×_V V_{j'}} ⇉ ∐ u^p h_{V_j} ⟶ u^p h_V
   is the overlap cofork of a fixed-target family 𝒰, restricted along u.
   The parallel arrows are u.op.whiskerLeft of toPresheafMap (overlapFst 𝒰) and
   toPresheafMap (overlapSnd 𝒰); the third arrow is
   (whiskerLeftOverlapCofork u 𝒰).π = u.op.whiskerLeft (augmentation 𝒰). -/
@[stacks 07GF] #check (whiskerLeftOverlapCofork u 𝒰)

#check (whiskerLeftOverlapCofork u 𝒰).π
