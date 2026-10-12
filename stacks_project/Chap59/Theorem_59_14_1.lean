/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
import ReasLib.CategoryTheory.Sites.AbelianSheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/- Theorem 59.14.1 (1): the category of abelian sheaves on a site is abelian. -/
@[stacks 03NU] #check
  (CategoryTheory.sheafAddCommGrpCat_abelian J : Abelian (Sheaf J AddCommGrpCat.{max u v}))

/- Theorem 59.14.1 (2): the category of abelian sheaves on a site has enough injectives. -/
@[stacks 03NU] #check
  (CategoryTheory.AbelianSheaf.enoughInjectives J :
    EnoughInjectives (Sheaf J AddCommGrpCat.{max u v}))
