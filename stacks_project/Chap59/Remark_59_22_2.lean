/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Limits.FormalCoproduct.Singleton.Over
import StacksCheckRecall

universe w v u

open CategoryTheory

/-
Remark 59.22.2 (03P0): in Lemma 59.22.1, the original covering family 𝒰
refines its coproduct singleton 𝒱 = {V ⟶ U}, not conversely in general.
Singleton coverings do not generally form an initial subcategory of the
category of all coverings of U.

Čech cohomology Ȟⁿ(U, F) is defined as the colimit, over the opposite of the
category of coverings 𝒰 of U, of the Čech cohomology groups of F with respect
to 𝒰. The source observes that it can nevertheless be computed in terms of
singleton coverings for sheaves, but explicitly defers a precise comparison
lemma. The check below asserts only the concrete refinement construction,
not initiality or that deferred sheaf-colimit comparison.
-/
@[stacks 03P0]
#check (CategoryTheory.Limits.FormalCoproduct.Over.toCoproductSingleton :
  ∀ {C : Type u} [Category.{v} C] {X : C}
    (K : CategoryTheory.Limits.FormalCoproduct.{w} (CategoryTheory.Over X))
    [CategoryTheory.Limits.HasCoproduct (fun i ↦ (K.obj i).left)],
    K ⟶ CategoryTheory.Limits.FormalCoproduct.Over.coproductSingleton K)
