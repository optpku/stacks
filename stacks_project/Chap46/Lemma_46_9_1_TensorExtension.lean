/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap46.Remark_46_3_15_AdequateCategory

@[expose] public section

open CategoryTheory

universe u

namespace ModuleValuedFunctor

/-- Every tensor-extension functor associated to an `A`-module is adequate. -/
theorem tensorExtension_adequate (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    Adequate (tensorExtension A) ((tensorExtension A).obj M) := sorry

namespace Adeq

/-- The tensor-extension functor, regarded as taking values in adequate
module-valued functors. -/
noncomputable def tensorExtension (A : CommRingCat.{u}) :
    ModuleCat.{u} A ⥤ Adeq A :=
  ObjectProperty.lift (Adequate (ModuleValuedFunctor.tensorExtension A))
    (ModuleValuedFunctor.tensorExtension A) (tensorExtension_adequate A)

/-- The underlying object of the lifted tensor-extension functor is the usual
tensor-extension functor. -/
theorem tensorExtension_obj (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    ((tensorExtension A).obj M).obj =
      (ModuleValuedFunctor.tensorExtension A).obj M := sorry

/-- The underlying morphism of the lifted tensor-extension functor is the usual
tensor-extension morphism. -/
theorem tensorExtension_map (A : CommRingCat.{u}) {M N : ModuleCat.{u} A}
    (f : M ⟶ N) :
    ((tensorExtension A).map f).hom =
      (ModuleValuedFunctor.tensorExtension A).map f := sorry

end Adeq

end ModuleValuedFunctor
