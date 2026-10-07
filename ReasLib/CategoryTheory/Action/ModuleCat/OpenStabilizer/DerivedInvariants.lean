module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.RepresentationTheory.Invariants
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Injective

@[expose] public section

universe u v

open CategoryTheory

namespace CategoryTheory.Action.ModuleCat.DiscreteModuleCat

variable (R : Type u) [CommRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The functor taking a discrete continuous module to its module of invariant elements. -/
noncomputable def fixedPointsFunctor : DiscreteModuleCat R G ⥤ ModuleCat.{max u v} R :=
  (openStabilizer R G).ι ⋙ Rep.ActionToRep R G ⋙ Rep.invariantsFunctor R G

/-- Taking invariant elements of discrete continuous modules is additive. -/
instance fixedPointsFunctor_additive : (fixedPointsFunctor R G).Additive := sorry

/-- The fixed-points functor evaluates to the invariant submodule of the underlying representation. -/
theorem fixedPointsFunctor_obj (M : DiscreteModuleCat R G) :
    (fixedPointsFunctor R G).obj M =
      ModuleCat.of R ((Rep.ActionToRep R G).obj M.obj).ρ.invariants := sorry

/-- Continuous module cohomology is the degree-indexed right derived functor of invariants. -/
noncomputable def derivedCohomologyFunctor (n : ℕ) :
    DiscreteModuleCat R G ⥤ ModuleCat.{max u v} R :=
  (fixedPointsFunctor R G).rightDerived n

end CategoryTheory.Action.ModuleCat.DiscreteModuleCat
