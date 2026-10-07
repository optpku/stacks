module

public import Mathlib.Topology.LocallyFinsupp
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap82.Definition_82_3_1_CycleGroup

/-!
# Closed-immersion pushforward of cycles on algebraic spaces

The inclusion of a closed subspace induces a weight-1 pushforward of
locally finite cycles by summing coefficients along the fibre of the map on
points. This realises `(i)_*` on cycle groups of a fixed relative dimension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inclusion of a closed subspace is a closed immersion. -/
instance ClosedSubspace.instIsClosedImmersion {S : Scheme.{u}} {X : AlgebraicSpace S}
    (W : ClosedSubspace X) : IsClosedImmersion W.ι :=
  W.isClosedImmersion

namespace Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
variable (f : X ⟶ B) (δ : Points B → ℤ)

/-- Weight-1 closed-immersion pushforward of a cycle has locally finite support. -/
theorem closedImmersionPushforwardCycle_locallyFiniteSupport
    (W : ClosedSubspace X) (α : Function.locallyFinsupp (Points W.X) ℤ) :
    LocallyFiniteSupport fun x : Points X ↦
      ∑ᶠ y ∈ Points.map W.ι ⁻¹' {x}, α y :=
  sorry

/-- The underlying locally finite cycle obtained by weight-1 pushforward along
the inclusion of a closed subspace. -/
def closedImmersionPushforwardCycle (W : ClosedSubspace X)
    (α : Function.locallyFinsupp (Points W.X) ℤ) :
    Function.locallyFinsupp (Points X) ℤ where
  toFun := fun x ↦ ∑ᶠ y ∈ Points.map W.ι ⁻¹' {x}, α y
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    closedImmersionPushforwardCycle_locallyFiniteSupport W α x

/-- Closed-immersion pushforward evaluates by a weight-1 finsum on the fibre of
`Points.map W.ι`. -/
theorem closedImmersionPushforwardCycle_apply (W : ClosedSubspace X)
    (α : Function.locallyFinsupp (Points W.X) ℤ) (x : Points X) :
    closedImmersionPushforwardCycle W α x =
      ∑ᶠ y ∈ Points.map W.ι ⁻¹' {x}, α y :=
  sorry

/-- Weight-1 pushforward along a closed subspace inclusion preserves relative
degree `k`. -/
theorem closedImmersionPushforward_mem_cycleGroup (W : ClosedSubspace X) (k : ℤ)
    (α : cycleGroup (W.ι ≫ f) δ k) :
    closedImmersionPushforwardCycle W
        (α : Function.locallyFinsupp (Points W.X) ℤ) ∈
      cycleGroup f δ k :=
  sorry

/-- The value of closed-immersion pushforward on a cycle of fixed relative
degree. -/
def closedImmersionPushforwardValue (W : ClosedSubspace X) (k : ℤ)
    (α : cycleGroup (W.ι ≫ f) δ k) : cycleGroup f δ k :=
  ⟨closedImmersionPushforwardCycle W (α : Function.locallyFinsupp (Points W.X) ℤ),
    closedImmersionPushforward_mem_cycleGroup f δ W k α⟩

/-- Closed-immersion pushforward sends the zero cycle to zero. -/
theorem closedImmersionPushforwardValue_zero (W : ClosedSubspace X) (k : ℤ) :
    closedImmersionPushforwardValue f δ W k 0 = 0 :=
  sorry

/-- Closed-immersion pushforward preserves addition of cycles. -/
theorem closedImmersionPushforwardValue_add (W : ClosedSubspace X) (k : ℤ)
    (α β : cycleGroup (W.ι ≫ f) δ k) :
    closedImmersionPushforwardValue f δ W k (α + β) =
      closedImmersionPushforwardValue f δ W k α +
        closedImmersionPushforwardValue f δ W k β :=
  sorry

/-- Pushforward of `k`-cycles along the closed immersion of a closed subspace. -/
def closedImmersionPushforward (W : ClosedSubspace X) (k : ℤ) :
    cycleGroup (W.ι ≫ f) δ k →+ cycleGroup f δ k where
  toFun := closedImmersionPushforwardValue f δ W k
  map_zero' := closedImmersionPushforwardValue_zero f δ W k
  map_add' := closedImmersionPushforwardValue_add f δ W k

/-- Closed-immersion pushforward evaluates by a weight-1 finsum on the fibre of
`Points.map W.ι`. -/
theorem closedImmersionPushforward_apply (W : ClosedSubspace X) (k : ℤ)
    (α : cycleGroup (W.ι ≫ f) δ k) (x : Points X) :
    (closedImmersionPushforward f δ W k α :
        Function.locallyFinsupp (Points X) ℤ) x =
      ∑ᶠ y ∈ Points.map W.ι ⁻¹' {x},
        (α : Function.locallyFinsupp (Points W.X) ℤ) y :=
  sorry

/-- Closed-immersion pushforward of the zero cycle is zero. -/
theorem closedImmersionPushforward_map_zero (W : ClosedSubspace X) (k : ℤ) :
    closedImmersionPushforward f δ W k 0 = 0 :=
  sorry

/-- Closed-immersion pushforward preserves addition. -/
theorem closedImmersionPushforward_map_add (W : ClosedSubspace X) (k : ℤ)
    (α β : cycleGroup (W.ι ≫ f) δ k) :
    closedImmersionPushforward f δ W k (α + β) =
      closedImmersionPushforward f δ W k α +
        closedImmersionPushforward f δ W k β :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace

