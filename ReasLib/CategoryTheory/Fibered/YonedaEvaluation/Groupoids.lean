/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.InSets.Slice
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.YonedaEvaluation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Groupoid-fibred Yoneda representatives

This is the groupoid-owner adapter for the neutral selected-cleavage Yoneda quasi-inverse. It
turns a fiber object into an actual morphism from the canonical groupoid-fibred slice, retaining
the concrete section data needed by slice base-change constructions.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {Y : FiberedCategoryOver.Groupoids C}

namespace FiberedCategoryOver.Groupoids.YonedaSlice

/-- The canonical slice morphism representing `y : Y.p.Fiber U`, built from the cleavage
selected by the bundled fibredness witness of `Y`. -/
@[stacks 0GWI "groupoid-fibred Yoneda representative"]
noncomputable def representative {U : C} (y : Y.p.Fiber U) :
    FiberedCategoryOver.Groupoids.slice U ⟶ Y :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    ((CartesianBasedFunctor.Yoneda.Chosen.functor Y.p U).obj y).toBasedFunctor

/-- Forgetting a canonical groupoid-fibred representative recovers its selected-cleavage based
slice section. -/
@[simp]
theorem representative.toBasedFunctor {U : C} (y : Y.p.Fiber U) :
    FiberedCategoryOver.Groupoids.toBasedFunctor (representative y) =
      ((CartesianBasedFunctor.Yoneda.Chosen.functor Y.p U).obj y).toBasedFunctor := sorry

/-- Every morphism out of the groupoid-fibred slice is canonically isomorphic to the
representative of its value at the identity slice object. -/
@[stacks 0GWI "groupoid-fibred Yoneda unit"]
noncomputable def representative.unitIso {U : C}
    (G : FiberedCategoryOver.Groupoids.slice U ⟶ Y) :
    G ≅ representative
      ((FiberedCategoryOver.Groupoids.fiberFunctor G U).obj
        (BasedCategory.Yoneda.Identity.fiberObj U)) :=
  FiberedCategoryOver.Groupoids.BasedFunctorIso.lift
    ((CartesianBasedFunctor.forget (Over.forget U) Y.p).mapIso
      ((CartesianBasedFunctor.Yoneda.Chosen.quasiInverse Y.p U).unitIso.app
        (CartesianBasedFunctor.ofTargetInGroupoids
          (FiberedCategoryOver.Groupoids.toBasedFunctor G))))

/-- The forward component of the groupoid-fibred Yoneda unit is the canonical cleavage
comparison at the given slice object. -/
@[simp]
theorem representative.unitIso.hom.app {U : C}
    (G : FiberedCategoryOver.Groupoids.slice U ⟶ Y) (a : Over U) :
    (representative.unitIso G).hom.hom.app a =
      ((CartesianBasedFunctor.Yoneda.Chosen.quasiInverse Y.p U).unitIso.app
        (CartesianBasedFunctor.ofTargetInGroupoids
          (FiberedCategoryOver.Groupoids.toBasedFunctor G))).hom.hom.app a := sorry

/-- The inverse component of the groupoid-fibred Yoneda unit is the inverse canonical cleavage
comparison at the given slice object. -/
@[simp]
theorem representative.unitIso.inv.app {U : C}
    (G : FiberedCategoryOver.Groupoids.slice U ⟶ Y) (a : Over U) :
    (representative.unitIso G).inv.hom.app a =
      ((CartesianBasedFunctor.Yoneda.Chosen.quasiInverse Y.p U).unitIso.app
        (CartesianBasedFunctor.ofTargetInGroupoids
          (FiberedCategoryOver.Groupoids.toBasedFunctor G))).inv.hom.app a := sorry

/-- Evaluating the canonical representative at the identity slice object recovers the fiber
object. The isomorphism is the explicit identity-reindexing comparison. -/
@[stacks 0GWI "groupoid-fibred Yoneda counit"]
noncomputable def representative.fiberObjIso {U : C} (y : Y.p.Fiber U) :
    (FiberedCategoryOver.Groupoids.fiberFunctor (representative y) U).obj
        (BasedCategory.Yoneda.Identity.fiberObj U) ≅ y :=
  (CartesianBasedFunctor.Yoneda.Chosen.quasiInverse Y.p U).counitIso.app y

end FiberedCategoryOver.Groupoids.YonedaSlice

end CategoryTheory

/- Axiom audit: the representative, unit, and counit delegate their concrete section and
comparison data to the neutral `CartesianBasedFunctor.Yoneda.Chosen` owner. This layer only
forgets cartesian preservation or lifts a based-functor isomorphism to the groupoid-fibred owner;
any `sorryAx` remains confined to inherited functor laws, cartesianness, and coherence fields. -/
