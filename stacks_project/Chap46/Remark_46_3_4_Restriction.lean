/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap46.Definition_46_3_2
public import stacks_project.Chap46.Lemma_46_3_6_TensorExtension

@[expose] public section

open CategoryTheory CommRingCat

universe u

namespace ModuleValuedFunctor

/-- The category of adequate module-valued functors on all `A`-algebras. -/
abbrev Adeq (A : CommRingCat.{u}) :=
  ObjectProperty.FullSubcategory (Adequate (tensorExtension A))

end ModuleValuedFunctor
