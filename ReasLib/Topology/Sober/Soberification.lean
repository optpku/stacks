/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.IrreducibleCloseds.Soberification.Functoriality
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Sober Targets of the Irreducible-Closed Soberification

This module records the canonical factorization of continuous maps through the
soberification when the target is sober.
-/

@[expose] public section

universe u v

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

section

variable {Y : Type v} [TopologicalSpace Y] [QuasiSober Y] [T0Space Y]

/-- The canonical order equivalence from irreducible closed subsets of a sober space to its
points is continuous for the soberification topology. -/
theorem continuous_irreducibleSetEquivPoints :
    Continuous (irreducibleSetEquivPoints (α := Y) : IrreducibleCloseds Y → Y) := sorry

/-- The inverse of the canonical equivalence from irreducible closed subsets of a sober space to
its points is continuous for the soberification topology. -/
theorem continuous_irreducibleSetEquivPoints_symm :
    Continuous ((irreducibleSetEquivPoints (α := Y)).toEquiv.symm :
      Y → IrreducibleCloseds Y) := sorry

/-- The canonical homeomorphism from the soberification of a sober space to the space itself. -/
noncomputable def irreducibleSetHomeomorphPoints : IrreducibleCloseds Y ≃ₜ Y :=
  Homeomorph.mk (irreducibleSetEquivPoints (α := Y)).toEquiv
    (continuous_irreducibleSetEquivPoints (Y := Y))
    (continuous_irreducibleSetEquivPoints_symm (Y := Y))

/-- The underlying function of the canonical factorization of a continuous map through the
soberification. -/
noncomputable def IrreducibleCloseds.soberificationLiftFun (f : C(X, Y))
    (T : IrreducibleCloseds X) : Y :=
  irreducibleSetEquivPoints (IrreducibleCloseds.map f f.continuous T)

/-- The canonical factorization through the soberification is continuous. -/
theorem IrreducibleCloseds.continuous_soberificationLiftFun (f : C(X, Y)) :
    Continuous (IrreducibleCloseds.soberificationLiftFun f) := sorry

/-- The canonical continuous factorization of a map from `X` to a sober space. -/
noncomputable def IrreducibleCloseds.soberificationLift (f : C(X, Y)) :
    C(IrreducibleCloseds X, Y) :=
  ⟨IrreducibleCloseds.soberificationLiftFun f,
    IrreducibleCloseds.continuous_soberificationLiftFun f⟩

/-- Evaluation of the canonical factor map through soberification. -/
@[simp]
theorem IrreducibleCloseds.soberificationLift_apply (f : C(X, Y))
    (T : IrreducibleCloseds X) :
    IrreducibleCloseds.soberificationLift f T =
      irreducibleSetEquivPoints (IrreducibleCloseds.map f f.continuous T) := sorry

/-- The canonical soberification factor extends the original continuous map. -/
@[simp]
theorem IrreducibleCloseds.soberificationLift_comp (f : C(X, Y)) :
    (IrreducibleCloseds.soberificationLift f).comp toIrreducibleCloseds = f := sorry

/-- A continuous map out of the soberification is determined by its composite with the canonical
map from `X`. -/
theorem IrreducibleCloseds.soberificationLift_unique (f : C(X, Y))
    (g : C(IrreducibleCloseds X, Y))
    (hg : g.comp toIrreducibleCloseds = f) :
    g = IrreducibleCloseds.soberificationLift f := sorry

/-- Lemma 5.8.16 (1): the soberification map is universal among continuous maps from `X` to
sober spaces, represented by Mathlib's `QuasiSober` and `T0Space` components. -/
@[stacks 0A2N "universal property for sober targets"]
theorem toIrreducibleCloseds_universal (f : C(X, Y)) :
    ∃! g : C(IrreducibleCloseds X, Y), g.comp toIrreducibleCloseds = f := sorry

end
