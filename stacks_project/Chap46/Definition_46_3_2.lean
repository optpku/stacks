/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy
public import stacks_project.Chap46.Definition_46_3_2_Instances
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

variable {A : CommRingCat.{u}}

/- Definition 46.3.2 (1): a module-valued functor is adequate when it has a kernel
presentation by a morphism of `A`-modules. -/
@[stacks 06UT] #check
  (ModuleValuedFunctor.Adequate (A := A) :
    (ModuleCat.{u} A ⥤ ModuleValuedFunctor.{u, v} A) →
      ModuleValuedFunctor.{u, v} A → Prop)

/- Definition 46.3.2 (2): a module-valued functor is linearly adequate when its kernel
presentation uses finite free powers of `A`. -/
@[stacks 06UT] #check
  (ModuleValuedFunctor.LinearlyAdequate (A := A) :
    (ModuleCat.{u} A ⥤ ModuleValuedFunctor.{u, v} A) →
      ModuleValuedFunctor.{u, v} A → Prop)
