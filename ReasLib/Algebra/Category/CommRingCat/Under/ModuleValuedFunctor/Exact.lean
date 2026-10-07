module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor
public import Mathlib.Algebra.Exact.Basic

@[expose] public section

universe u v

namespace ModuleValuedFunctor.Hom

variable {A : CommRingCat.{u}} {F G H : ModuleValuedFunctor.{u, v} A}

/-- A composable pair of morphisms of module-valued functors is pointwise short exact
when its components are injective, exact, and surjective over every algebra. -/
def IsPointwiseShortExact (f : Hom F G) (g : Hom G H) : Prop :=
  ∀ B, Function.Injective (f.app B) ∧ Function.Exact (f.app B) (g.app B) ∧
    Function.Surjective (g.app B)

end ModuleValuedFunctor.Hom
