module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Sites.Limits
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

noncomputable section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (ℱ : Sheaf J (Type w))

/- Definition 7.30.4 (1): the topos `Over ℱ` is the localization of the topos `Sh(C, J)` at `ℱ`. -/
@[stacks 04IP] #check (Over ℱ)

/- Definition 7.30.4 (2): the morphism of topoi `Over.forgetAdjStar ℱ` of Lemma 7.30.1 is the
localization morphism. -/
@[stacks 04IP] #check (Over.forgetAdjStar ℱ : Over.forget ℱ ⊣ Over.star ℱ)

/- The lower-shriek functor of the localization morphism is the slice forgetful functor. -/
#check Over.forget ℱ

/- The inverse-image functor of the localization morphism is `Over.star ℱ`. -/
#check Over.star ℱ
