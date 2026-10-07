module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Injectives
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Restriction
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.TensorExtension
public import ReasLib.Algebra.Category.ModuleCat.Pure

@[expose] public section

open CategoryTheory

universe u

namespace ModuleValuedFunctor.TensorAdeq

/-- An object of the tensor-adequate category is injective exactly when it is
isomorphic to the tensor extension of a pure-injective module. -/
theorem injective_iff_pureInjective_tensorExtension (A : CommRingCat.{u}) (F : TensorAdeq A) :
    CategoryTheory.Injective F ↔
      ∃ I : ModuleCat.{u} A,
        I.PureInjective ∧ Nonempty (F.obj ≅ (tensorExtensionFunctor A).obj I) := sorry

end ModuleValuedFunctor.TensorAdeq
