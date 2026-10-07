module

public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Exact tensor functors and flat modules

Flatness and faithful flatness of a module are characterized by exactness and faithfulness of
the functor that tensors with the module on the right.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe u

namespace Module.Flat

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

/-- A module is flat exactly when tensoring with it on the right is an exact functor. -/
theorem iff_exactFunctor_tensorRight :
    Module.Flat R M ↔
      exactFunctor (ModuleCat.{u} R) (ModuleCat.{u} R) (tensorRight M) := sorry

end Module.Flat

namespace Module.FaithfullyFlat

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

/-- A module is faithfully flat exactly when tensoring with it on the right is exact and
faithful. -/
theorem iff_exactFunctor_and_faithful_tensorRight :
    Module.FaithfullyFlat R M ↔
      exactFunctor (ModuleCat.{u} R) (ModuleCat.{u} R) (tensorRight M) ∧
        (tensorRight M).Faithful := sorry

end Module.FaithfullyFlat
