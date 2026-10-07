module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Duality
public import ReasLib.CategoryTheory.Monoidal.Closed.Duality.HomotopyColimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfect duals and sequential homotopy colimits

This leaf records the source-facing tensor-dual inverse system for a sequential diagram of
perfect derived modules and its homotopy-limit comparison.  The generic closed-monoidal
hocolimit theorem remains the underlying categorical owner; the displayed tower keeps the
module-category `RHom` and derived-tensor choices visible for downstream source statements.

@stack 0BKB
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory.InternalHom
open CategoryTheory.MonoidalCategory
open scoped _root_.DerivedInternalHom

namespace CategoryTheory.DerivedCategory.Perfect.Duality

variable {A : Type u} [CommRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat A))]
variable [BraidedCategory (DerivedCategory (ModuleCat A))]
variable [RHom.Has (A := A)]
variable [DerivedTensor.Right.Has (C := ModuleCat A)]

local notation "DMod" => DerivedCategory (ModuleCat A)

/-- Lemma 15.75.17 (0BKB): the explicit inverse system of derived tensor products with stage
duals, for a sequential diagram `K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` and a fixed target `E`. -/
@[stacks 0BKB "source-facing tensor-dual inverse system"]
abbrev dualTensorInverseSystem
    (M : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ DMod)
    (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) :
    SequentialInverseSystem DMod :=
  let _ := s
  let X : ℕ → DMod := fun n =>
    (DerivedTensor.Right.functor (selectedDual M (K n))).obj E
  Functor.ofOpSequence <| fun n ↦
    show X (n + 1) ⟶ X n from
      (DerivedTensor.Right.Closed.tensorMapOf M.closed M.tensorModel
        (selectedDualMap M (f n))).app E

/-- Lemma 15.75.17 (0BKB): `RHom` of a sequential homotopy colimit is represented by the
homotopy limit of the tensor-dual inverse system. -/
@[stacks 0BKB "RHom of a homotopy colimit as a homotopy limit"]
theorem rhom_isHomotopyLimit_of_homotopyColimit
    (M : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ DMod)
    (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) (Khocolim : DMod)
    (hKhocolim : HomotopyColimit.IsOf (Functor.ofSequence f) Khocolim)
    (hperfect : ∀ n, (K n).IsPerfect) (E : DMod) :
    HomotopyLimit.IsOf
      (dualTensorInverseSystem M s E K f)
      (RHom[M.closed](Khocolim, E)) := sorry

end CategoryTheory.DerivedCategory.Perfect.Duality

end
