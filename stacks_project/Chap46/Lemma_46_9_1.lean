module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.InjectiveCharacterization
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 46.9.1 -/
@[stacks 0708] #check (ModuleValuedFunctor.TensorAdeq.injective_iff_pureInjective_tensorExtension :
  ∀ (A : CommRingCat.{u}) (F : ModuleValuedFunctor.TensorAdeq A),
    CategoryTheory.Injective F ↔
      ∃ I : ModuleCat.{u} A,
        I.PureInjective ∧
          Nonempty (F.obj ≅ (ModuleValuedFunctor.tensorExtensionFunctor A).obj I))
