/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap46.Definition_46_3_2
public import stacks_project.Chap46.Lemma_46_3_6_TensorExtension

@[expose] public section

open CategoryTheory

universe u

namespace ModuleValuedFunctor

/-- The full category of adequate module-valued functors on `Alg_A`. -/
abbrev Adeq (A : CommRingCat.{u}) :=
  ObjectProperty.FullSubcategory (Adequate (tensorExtension A))

namespace Adeq

/-- Every object of `ModuleValuedFunctor.Adeq A` is adequate. -/
theorem adequate {A : CommRingCat.{u}} (F : Adeq A) :
    Adequate (tensorExtension A) F.obj := sorry

end Adeq

end ModuleValuedFunctor
