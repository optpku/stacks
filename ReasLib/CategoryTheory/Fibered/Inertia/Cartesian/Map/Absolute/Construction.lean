/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Detection.Absolute
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Objects.Construction
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cartesian maps for absolute inertia

This file owns the cartesian lifts of the neutral absolute-inertia map, both for
heterogeneous cartesian based functors and for morphisms of fibred categories.
Computations and pseudofunctor comparisons are layered separately.
-/

@[expose] public section

universe u v uS vS uT vT w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace CartesianBasedFunctor.Inertia

variable {C : Type u} [Category.{v} C]
variable {S : Type uS} {T : Type uT}
variable [Category.{vS} S] [Category.{vT} T]
variable {p : S ⥤ C} {q : T ⥤ C} [p.IsFibered]

namespace map

/-- The neutral absolute-inertia map of a heterogeneous cartesian functor preserves strongly
cartesian arrows. Fibredness is required only of the source projection. -/
@[stacks 04Z4 "heterogeneous cartesian inertia map preservation"]
theorem preservesStronglyCartesian (F : CartesianBasedFunctor p q) :
    (BasedCategory.Inertia.map F.toBasedFunctor).PreservesStronglyCartesian := sorry

end map

/-- A heterogeneous cartesian functor induces a heterogeneous cartesian functor between the
explicit absolute-inertia projections. -/
@[stacks 04Z4 "heterogeneous cartesian absolute-inertia map"]
def map (F : CartesianBasedFunctor p q) :
    CartesianBasedFunctor
      (BasedCategory.inertia (BasedCategory.ofFunctor p)).p
      (BasedCategory.inertia (BasedCategory.ofFunctor q)).p :=
  CartesianBasedFunctor.ofBasedFunctor
    (BasedCategory.Inertia.map F.toBasedFunctor)
    (map.preservesStronglyCartesian F)

end CartesianBasedFunctor.Inertia

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

namespace map

/-- The based map on inertia induced by a morphism of fibred categories preserves strongly
cartesian morphisms. -/
@[stacks 04Z4 "cartesian inertia map preservation"]
theorem preservesStronglyCartesian (F : X ⟶ Y) :
    (BasedCategory.Inertia.map
      (FiberedCategoryOver.toBasedFunctor F)).PreservesStronglyCartesian := sorry
/- Proof strategy: apply `BasedCategory.Inertia.map.preservesStronglyCartesian`; fibredness comes
from the two bundled objects and preservation from the hom-property field of `F`. -/

end map

/-- A morphism of fibred categories induces a morphism between their absolute inertias. -/
@[stacks 04Z4 "(2) cartesian absolute-inertia map"]
def map (F : X ⟶ Y) :
    FiberedCategoryOver.inertia X ⟶ FiberedCategoryOver.inertia Y :=
  FiberedCategoryOver.ofBasedFunctor
    (BasedCategory.Inertia.map (FiberedCategoryOver.toBasedFunctor F))
    (map.preservesStronglyCartesian F)

end FiberedCategoryOver.Inertia

end CategoryTheory

/- Axiom audit: the heterogeneous and fixed cartesian maps store
`BasedCategory.Inertia.map F.toBasedFunctor` definitionally. Any new `sorryAx` is confined to
strongly-cartesian-preservation or owner-membership proof fields. -/
