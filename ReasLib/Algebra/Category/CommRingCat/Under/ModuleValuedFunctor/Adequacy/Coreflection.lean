module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Restriction
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Generators
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Colimits

@[expose] public section

open CategoryTheory

universe u

namespace ModuleValuedFunctor.TensorAdequate

/-- Every module-valued functor admits a universal morphism from a tensor-adequate
module-valued functor. -/
theorem exists_coreflection (A : CommRingCat.{u})
    (F : ModuleValuedFunctor.bundled.{u, u} A) :
    ∃ (Q : ModuleValuedFunctor.TensorAdeq A) (q : Q.obj ⟶ F),
      ∀ G : ModuleValuedFunctor.TensorAdeq A,
        Function.Bijective (fun f : G.obj ⟶ Q.obj ↦ f ≫ q) := sorry

end ModuleValuedFunctor.TensorAdequate
