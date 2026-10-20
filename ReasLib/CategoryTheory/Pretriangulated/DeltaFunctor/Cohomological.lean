module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Sequence
public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Definition
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomological Delta Functors from Pretriangulated Delta Functors

This module bridges a delta functor into a pretriangulated category to the
cohomological delta functor induced by a homological functor on that target.
-/

@[expose] public section

namespace CategoryTheory.DeltaFunctor

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe vA vB vD uA uB uD

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

variable (G : DeltaFunctor A D) (H : D ⥤ B)
variable [H.IsHomological] [H.ShiftSequence ℤ]

/-- The degree-`n` additive functor obtained by composing a `DeltaFunctor` with
the degree-`n` shift of a homological functor. -/
abbrev cohomologyFunctor (n : ℤ) : A ⥤+ B :=
  ⟨G.toFunctor ⋙ H.shift n,
    ⟨fun {X Y} {f g : X ⟶ Y} ↦ by
      change (H.shift n).map (G.map (f + g)) =
        (H.shift n).map (G.map f) + (H.shift n).map (G.map g)
      rw [G.additive.map_add]
      exact (AdditiveFunctor.of (H.shift n)).property.map_add⟩⟩

/-- The degree-`n` connecting morphism induced by a homological functor on the
triangle attached to a short exact sequence. -/
noncomputable def cohomologyConnecting {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (H.shift (n : ℤ)).obj (G.obj S.X₃) ⟶
      (H.shift ((n + 1 : ℕ) : ℤ)).obj (G.obj S.X₁) := by
  simpa [triangle] using
    H.homologySequenceδ (G.triangle hS) (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp)

/-- A delta functor followed degreewise by a homological functor is a cohomological
delta functor when its degree-`-1` term vanishes on the source. -/
@[stacks 05SR]
noncomputable def toCohomologicalDeltaFunctor
    (hneg : ∀ X : A, IsZero ((H.shift (-1)).obj (G.obj X))) :
    CohomologicalDeltaFunctor A B where
  F := fun n ↦ G.cohomologyFunctor H (n : ℤ)
  δ := fun {S} hS n ↦ G.cohomologyConnecting H hS n
  mono_map_f_zero := fun {S} hS ↦ by
    have hδ : H.homologySequenceδ (G.triangle hS) (-1) 0 (by simp) = 0 := by
      exact (hneg S.X₃).eq_of_src _ _
    exact (H.homologySequence_mono_shift_map_mor₁_iff
      (G.triangle hS) (G.triangle_distinguished hS) (-1) 0 (by simp)).2 (by
        simpa [triangle] using hδ)
  exact₅ := fun {_} hS n ↦ by
    convert H.homologySequenceComposableArrows₅_exact
      (G.triangle hS) (G.triangle_distinguished hS) (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp) using 1
    all_goals simp [cohomologyFunctor, cohomologyConnecting, triangle]
    all_goals rfl
  δ_naturality := fun {_ _} hS hT φ n ↦ by
    refine CommSq.mk ?_
    convert H.homologySequenceδ_naturality
      (G.triangle hS) (G.triangle hT) (G.triangleMap hS hT φ)
      (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp) using 1
    all_goals simp [cohomologyFunctor, cohomologyConnecting, triangle]
    all_goals rfl

end

end CategoryTheory.DeltaFunctor
