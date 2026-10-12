/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.RingTheory.AdicCompletion.Evaluation

@[expose] public section

noncomputable section

universe u v

namespace Ideal.PowerAnnihilated

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The action of a quotient scalar on an element annihilated by the corresponding
power of the ideal, viewed in the ambient module. -/
def quotientAction (I : Ideal R) (n : ℕ) (a : R ⧸ I ^ n)
    (x : I.powerAnnihilatedSubmodule M n) : M :=
  ((a • x : I.powerAnnihilatedSubmodule M n) : M)

/-- The finite-stage quotient action of the class of `r` agrees with the original
`R`-action. -/
theorem quotientAction_mk (I : Ideal R) (n : ℕ) (r : R)
    (x : I.powerAnnihilatedSubmodule M n) :
    quotientAction I n (Ideal.Quotient.mk (I ^ n) r) x = r • x := sorry

end Ideal.PowerAnnihilated

namespace Module.IsIdealPowerTorsion

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The underlying action of a completed scalar on an ideal-power-torsion element. -/
noncomputable def completionAction (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) (a : AdicCompletion I R) (x : M) : M :=
  let hx : x ∈ Ideal.primaryComponent M I := by
    rw [hM]
    exact Submodule.mem_top
  let hx := (Ideal.primaryComponent_mem M I x).mp hx
  let n := Classical.choose hx
  Ideal.PowerAnnihilated.quotientAction I n (AdicCompletion.evalₐ I n a)
    ⟨x, Classical.choose_spec hx⟩

/-- The completed-scalar action is additive in the module argument. -/
theorem completionAction_add (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) (a : AdicCompletion I R) (x y : M) :
    completionAction I hM a (x + y) =
      completionAction I hM a x + completionAction I hM a y := sorry

/-- The completed-scalar action respects the original `R`-scalar multiplication. -/
theorem completionAction_smul (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) (a : AdicCompletion I R) (r : R) (x : M) :
    completionAction I hM a (r • x) = r • completionAction I hM a x := sorry

/-- A completed scalar acting as an `R`-linear endomorphism. -/
noncomputable def completionEnd (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) (a : AdicCompletion I R) : Module.End R M where
  toFun := completionAction I hM a
  map_add' := completionAction_add I hM a
  map_smul' := completionAction_smul I hM a

/-- Zero acts by the zero endomorphism. -/
theorem completionEnd_zero (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) :
    completionEnd I hM 0 = 0 := sorry

/-- Addition of completed scalars acts by addition of endomorphisms. -/
theorem completionEnd_add (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) (a b : AdicCompletion I R) :
    completionEnd I hM (a + b) = completionEnd I hM a + completionEnd I hM b := sorry

/-- One acts by the identity endomorphism. -/
theorem completionEnd_one (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) :
    completionEnd I hM 1 = 1 := sorry

/-- Multiplication of completed scalars acts by composition of endomorphisms. -/
theorem completionEnd_mul (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) (a b : AdicCompletion I R) :
    completionEnd I hM (a * b) = completionEnd I hM a * completionEnd I hM b := sorry

/-- The canonical action of the `I`-adic completion on an `I`-power-torsion module,
as a ring homomorphism into its ring of `R`-linear endomorphisms. -/
noncomputable def completionToEnd (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) :
    AdicCompletion I R →+* Module.End R M where
  toFun := completionEnd I hM
  map_one' := completionEnd_one I hM
  map_mul' := completionEnd_mul I hM
  map_zero' := completionEnd_zero I hM
  map_add' := completionEnd_add I hM

/-- The completion action on an element may be evaluated at any ideal-power stage
that annihilates that element. -/
theorem completionToEnd_apply_of_mem_stage (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) (a : AdicCompletion I R)
    (n : ℕ) (x : M) (hx : x ∈ I.powerAnnihilatedSubmodule M n) :
    completionToEnd I hM a x =
      Ideal.PowerAnnihilated.quotientAction I n (AdicCompletion.evalₐ I n a) ⟨x, hx⟩ := sorry

/-- The completion action extends the original scalar action along the canonical
map from `R` to its `I`-adic completion. -/
theorem completionToEnd_comp_algebraMap (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) :
    (completionToEnd I hM).comp (algebraMap R (AdicCompletion I R)) =
      Module.toModuleEnd R M := sorry

end Module.IsIdealPowerTorsion
