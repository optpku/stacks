/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/- Theorem 19.7.4 (1): abelian sheaves on a site have enough injectives. -/
@[stacks 01DP] #check
  (inferInstance : EnoughInjectives
    (Sheaf J AddCommGrpCat.{max u v}))

/- Theorem 19.7.4 (2): the injective embeddings can be chosen functorially. -/
@[stacks 01DP] #check
  (inferInstance : HasFunctorialInjectives
    (Sheaf J AddCommGrpCat.{max u v}))

#check @CategoryTheory.AbelianSheaf.isGrothendieckAbelian
#check @CategoryTheory.AbelianSheaf.hasFunctorialInjectives
