/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite.Closure
import StacksCheckRecall

/-!
# Lemma 18.43.5 compatibility entry point

The closure properties of finite locally constant sheaves are owned by
`ReasLib.CategoryTheory.Sites.LocallyConstant.Finite.Closure`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v w u₁

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Types

variable [HasWeakSheafify J (Type w)]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]
variable (K : Type u₁) [SmallCategory K] [FinCategory K]

/- Lemma 18.43.5 (1), finite-limit part: finite locally constant set-valued sheaves are closed
under finite limits. -/
@[stacks 093U "(1), finite limits"]
#check (inferInstance :
  IsClosedUnderLimitsOfShape (finiteLocallyConstant J) K)

/- Lemma 18.43.5 (1), finite-colimit part: finite locally constant set-valued sheaves are closed
under finite colimits. -/
@[stacks 093U "(1), finite colimits"]
#check (inferInstance :
  IsClosedUnderColimitsOfShape (finiteLocallyConstant J) K)

end Types

section AddCommGroups

variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [Abelian (Sheaf J AddCommGrpCat.{w})]

/- Lemma 18.43.5 (2): finite locally constant abelian sheaves form a weak Serre class. -/
@[stacks 093U "(2)"]
#check (inferInstance :
  IsWeakSerreClass (finiteLocallyConstantAddCommGrp J))

end AddCommGroups

section Modules

variable {R : Type w} [Ring R] [IsNoetherianRing R]
variable [HasWeakSheafify J (ModuleCat.{w} R)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} R)]
variable [Abelian (Sheaf J (ModuleCat.{w} R))]

/- Lemma 18.43.5 (3): over a Noetherian ring, finite-type locally constant module sheaves form
a weak Serre class. -/
@[stacks 093U "(3)"]
#check (inferInstance :
  IsWeakSerreClass (finiteTypeLocallyConstantModule J R))

end Modules

end CategoryTheory.Sheaf
