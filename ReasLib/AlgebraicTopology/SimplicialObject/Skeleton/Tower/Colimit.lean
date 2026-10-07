module

public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.Tower
public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.FiniteConnected
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

/-!
@stack 0193

# Colimit of the skeleton tower

Evaluation at a simplex is eventually constant along the skeleton tower.  The canonical cocone
is therefore a colimit degreewise and hence in the simplicial-object functor category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Skeleton

variable {A : Type u} [Category.{v} A]
variable [∀ n, SimplicialObject.Truncated.HasPointwiseSkeletons A n]

/-- In every degree at most `n`, the corresponding component of the `n`-skeleton cocone leg is
an isomorphism. -/
@[stacks 0193 "skeleton cocone components are isomorphisms below the stage"]
theorem cocone_ι_app_isIso_of_le (V : SimplicialObject A)
    (Δ : SimplexCategoryᵒᵖ) {n : ℕ} (h : Δ.unop.len ≤ n) :
    IsIso (((cocone V).ι.app n).app Δ) := sorry

/-- Evaluation of the skeleton sequence at `Δ` is constant from degree `Δ.unop.len`
onward. -/
@[stacks 0193 "degreewise skeleton sequence is eventually constant"]
theorem evaluation.isEventuallyConstantFrom (V : SimplicialObject A)
    (Δ : SimplexCategoryᵒᵖ) :
    Functor.IsEventuallyConstantFrom
      (sequence V ⋙ (evaluation _ A).obj Δ) Δ.unop.len := sorry

/-- Evaluation at `Δ` sends the canonical skeleton cocone to a colimit cocone. -/
@[stacks 0193 "degreewise colimit of the skeleton tower"]
noncomputable def evaluation.isColimit (V : SimplicialObject A)
    (Δ : SimplexCategoryᵒᵖ) :
    IsColimit (((evaluation _ A).obj Δ).mapCocone (cocone V)) :=
  @Functor.IsEventuallyConstantFrom.isColimitOfIsIso
    ℕ A _ _ (sequence V ⋙ (evaluation _ A).obj Δ) Δ.unop.len
    (evaluation.isEventuallyConstantFrom V Δ) _
    (((evaluation _ A).obj Δ).mapCocone (cocone V))
    (cocone_ι_app_isIso_of_le V Δ (Nat.le_refl _))

/-- 0193 (Lemma 14.22.5 (1)): a simplicial object is the colimit of its canonical skeleton
tower. -/
@[stacks 0193]
noncomputable def isColimit (V : SimplicialObject A) : IsColimit (cocone V) :=
  evaluationJointlyReflectsColimits (cocone V) (evaluation.isColimit V)

namespace Tower

/-- The identity endofunctor is the colimit of the functorial skeleton tower. This is the
natural-in-`V` form of `Skeleton.isColimit V`. -/
@[stacks 0193 "functorial colimit of the skeleton tower"]
noncomputable def isColimit : IsColimit (cocone (A := A)) :=
  evaluationJointlyReflectsColimits (cocone (A := A))
    (fun V ↦ Skeleton.isColimit V)

end Tower

end CategoryTheory.SimplicialObject.Skeleton
