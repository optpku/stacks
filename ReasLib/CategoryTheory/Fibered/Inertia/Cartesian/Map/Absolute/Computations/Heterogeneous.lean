/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Absolute.Construction

/-!
# Computations for heterogeneous cartesian absolute-inertia maps

This leaf records the based and total projections of the heterogeneous cartesian map owner.
-/

@[expose] public section

universe u v uS vS uT vT uU vU w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace CartesianBasedFunctor.Inertia.map

variable {C : Type u} [Category.{v} C]
variable {S : Type uS} {T : Type uT}
variable [Category.{vS} S] [Category.{vT} T]
variable {p : S ⥤ C} {q : T ⥤ C} [p.IsFibered]

/-- Forgetting cartesian preservation from the heterogeneous inertia map recovers the canonical
based inertia map. -/
@[simp, stacks 04Z4 "underlying heterogeneous inertia map"]
theorem toBasedFunctor (F : CartesianBasedFunctor p q) :
    (map F).toBasedFunctor = BasedCategory.Inertia.map F.toBasedFunctor := sorry

/-- The total functor underlying the heterogeneous inertia map is the neutral inertia-map
functor. -/
@[simp, stacks 04Z4 "underlying total heterogeneous inertia functor"]
theorem toFunctor (F : CartesianBasedFunctor p q) :
    (map F).toFunctor = (BasedCategory.Inertia.map F.toBasedFunctor).toFunctor := sorry

/-- A heterogeneous cartesian inertia map applies the original functor to the underlying object. -/
@[simp, stacks 04Z4 "heterogeneous absolute-inertia object computation"]
theorem obj (F : CartesianBasedFunctor p q)
    (A : (BasedCategory.inertia (BasedCategory.ofFunctor p)).obj) :
    ((map F).toFunctor.obj A).obj = F.toFunctor.obj A.obj := sorry

/-- A heterogeneous cartesian inertia map applies the original functor to the selected
automorphism. -/
@[simp, stacks 04Z4 "heterogeneous absolute-inertia automorphism computation"]
theorem aut (F : CartesianBasedFunctor p q)
    (A : (BasedCategory.inertia (BasedCategory.ofFunctor p)).obj) :
    ((map F).toFunctor.obj A).aut = F.toFunctor.mapIso A.aut := sorry

/-- A heterogeneous cartesian inertia map applies the original functor to the underlying arrow. -/
@[simp, stacks 04Z4 "heterogeneous absolute-inertia arrow computation"]
theorem hom (F : CartesianBasedFunctor p q)
    {A B : (BasedCategory.inertia (BasedCategory.ofFunctor p)).obj} (φ : A ⟶ B) :
    CategoryTheory.RelativeInertia.hom ((map F).toFunctor.map φ) =
      F.toFunctor.map (CategoryTheory.RelativeInertia.hom φ) := sorry

/-- The heterogeneous cartesian inertia map sends a cartesian identity to the identity map. -/
@[simp, stacks 04Z4 "heterogeneous absolute-inertia identity computation"]
theorem id (p : S ⥤ C) [p.IsFibered] :
    map (CartesianBasedFunctor.id p) =
      CartesianBasedFunctor.id (BasedCategory.inertia (BasedCategory.ofFunctor p)).p := sorry

/-- The heterogeneous cartesian inertia map preserves composition of cartesian functors. -/
@[simp, stacks 04Z4 "heterogeneous absolute-inertia composition computation"]
theorem comp
    {U : Type uU} [Category.{vU} U] {r : U ⥤ C} [q.IsFibered]
    (F : CartesianBasedFunctor p q) (G : CartesianBasedFunctor q r) :
    map (CartesianBasedFunctor.comp F G) =
      CartesianBasedFunctor.comp (map F) (map G) := sorry

end CartesianBasedFunctor.Inertia.map

end CategoryTheory
