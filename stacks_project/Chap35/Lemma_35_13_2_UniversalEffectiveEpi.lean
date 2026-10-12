/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Family.UniversalEffectiveEpi
import StacksCheckRecall

@[expose] public section

universe w v u

/- Definition 7.12.1: a fixed-target family is universally effective epimorphic when it is
effective epimorphic after every base change. -/
@[stacks 00WP]
#check
  (@CategoryTheory.SemiRepresentableFamily.Over.IsUniversalEffectiveEpiFamily.{w, v, u} :
    ∀ {C : Type u} [CategoryTheory.Category.{v} C] {U : C},
      CategoryTheory.SemiRepresentableFamily.Over.{w} U → Prop)
