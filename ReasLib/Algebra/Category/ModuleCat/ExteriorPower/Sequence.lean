module

public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.Epi
public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.LeftTensor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Right-exact exterior-power sequences in `ModuleCat`

The canonical short complex is separated from its exactness and epimorphicity properties so each
piece can be reused independently.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace ModuleCat.exteriorPower

variable {R : Type u} [CommRing R]

/-- The two morphisms in the exterior-power sequence associated to `S` compose to zero. -/
theorem sequenceCompEqZero (S : ShortComplex (ModuleCat.{u} R)) (n : ℕ) :
    leftTensorMap S.f n ≫ map S.g (n + 1) = 0 := sorry

/-- The canonical exterior-power short complex in degree `n + 1`. -/
@[stacks 00DO "exterior-power sequence in ModuleCat"]
noncomputable def sequence (S : ShortComplex (ModuleCat.{u} R)) (n : ℕ) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (leftTensorMap S.f n) (map S.g (n + 1))
    (sequenceCompEqZero S n)

/-- An exact pair ending in an epimorphism induces an exact exterior-power pair. -/
@[stacks 00DO "exact exterior-power sequence in ModuleCat"]
theorem sequence_exact (S : ShortComplex (ModuleCat.{u} R)) (n : ℕ)
    (hS : S.Exact) [Epi S.g] :
    (sequence S n).Exact := sorry

/-- The final morphism in the exterior-power sequence is epimorphic whenever `S.g` is. -/
instance sequence_epi (S : ShortComplex (ModuleCat.{u} R)) (n : ℕ) [Epi S.g] :
    Epi (sequence S n).g := sorry

/-- The exterior-power sequence associated to an exact pair ending in an epimorphism is right
exact. -/
@[stacks 00DO "right-exact exterior-power sequence in ModuleCat"]
theorem sequence_exact_and_epi (S : ShortComplex (ModuleCat.{u} R)) (n : ℕ)
    (hS : S.Exact) [Epi S.g] :
    (sequence S n).Exact ∧ Epi (sequence S n).g := sorry

end ModuleCat.exteriorPower
