module

public import ReasLib.AlgebraicGeometry.ChowMotive
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory.Linear
public import ReasLib.CategoryTheory.Idempotents.Karoubi.Linear
public import Mathlib.Algebra.Category.ModuleCat.Images

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Correspondence

noncomputable section

universe u

namespace ChowMotive

variable {k : Type u} [Field k]

/-- The degree arithmetic used by the rational Chow realization. -/
theorem chowRealization_degree (i : ℤ) (X Y : Correspondence.GradedCategory k) :
    i + X.2 + (Y.2 - X.2) = i + Y.2 := by
  ring

/-- The degree-`i` rational Chow realization of graded correspondences.

An object `(X, m)` is sent to `CH^(i + m)(X) ⊗ ℚ`.  A correspondence acts by
the existing rational correspondence pushforward, followed by the canonical
transport to the target degree.
-/
def chowRealization (k : Type u) [Field k] (i : ℤ) :
    Correspondence.GradedCategory k ⥤ ModuleCat.{u + 1} ℚ where
  obj X := ModuleCat.of ℚ (RationalChowCohomology X.1.scheme (i + X.2))
  map {X Y} c := ModuleCat.ofHom
    ((castCohomologyDegree (chowRealization_degree i X Y)).comp
      (pushforward X.1.scheme Y.1.scheme (Y.2 - X.2) (i + X.2) c))
  map_id := sorry
  map_comp := sorry

/-- Computation of the degreewise Chow realization on a correspondence. -/
theorem chowRealization_map_apply (i : ℤ)
    {X Y : Correspondence.GradedCategory k} (c : X ⟶ Y)
    (alpha : RationalChowCohomology X.1.scheme (i + X.2)) :
    ((chowRealization k i).map c).hom alpha =
      castCohomologyDegree (chowRealization_degree i X Y)
        (pushforward X.1.scheme Y.1.scheme (Y.2 - X.2) (i + X.2) c alpha) :=
  rfl

/-- The `i`th Chow group of a rational Chow motive is the image of its projector
under the concrete degree-`i` rational Chow realization. -/
def chowGroup (M : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) (i : ℤ) :
    ModuleCat.{u + 1} ℚ :=
  ModuleCat.image ((chowRealization k i).map M.p)

/-- The carrier of a motive's Chow group is the range of its projector action. -/
theorem chowGroup_eq_range
    (M : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) (i : ℤ) :
    chowGroup M i =
      ModuleCat.of ℚ (LinearMap.range ((chowRealization k i).map M.p).hom) :=
  rfl

end ChowMotive
