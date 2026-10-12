/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module fibers at closed points

For a closed point `x` of `Spec(R)`, this leaf owns the quotient presentation
`M(x) = M / xM`, its residue-field vector-space structure, and the comparison with the canonical
tensor fiber `κ(x) ⊗[R] M`.

@stack 0GV8
-/

@[expose] public section

open scoped TensorProduct

universe u v

set_option quotPrecheck false in
scoped[ClosedPointFiber] notation:max "κ(" x:max ")" =>
  Ideal.ResidueField ((x).1.asIdeal)

namespace Module

variable {R : Type u} [CommRing R]

/-- Situation 15.128.1 (1), tag 0GV8: the fiber of an `R`-module `N` at a closed point `x` is
the quotient `N / xN`. -/
@[stacks 0GV8 "closed-point module fiber"]
abbrev ClosedPointFiber (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) : Type v :=
  N ⧸ x.1.asIdeal • (⊤ : Submodule R N)

end Module

scoped[ClosedPointFiber] notation:max N:max "﹙" x:max "﹚" =>
  Module.ClosedPointFiber N x

namespace Module.ClosedFiber

variable {R : Type u} [CommRing R]

open scoped ClosedPointFiber

/-- The prime ideal represented by a closed point of `Spec(R)` is maximal. -/
@[stacks 0GV8 "closed points correspond to maximal ideals"]
instance isMaximal (x : closedPoints (PrimeSpectrum R)) : x.1.asIdeal.IsMaximal := sorry
-- Proof strategy: apply `PrimeSpectrum.isClosed_singleton_iff_isMaximal` to the closed-singleton
-- witness carried by `x : closedPoints (PrimeSpectrum R)`.

/-- The quotient ring `R / x` is canonically equivalent to the residue field `κ(x)`. -/
@[stacks 0GV8 "closed-point quotient and residue field"]
noncomputable abbrev residueFieldAlgEquiv (x : closedPoints (PrimeSpectrum R)) :
    (R ⧸ x.1.asIdeal) ≃ₐ[R] κ(x) :=
  Ideal.ResidueField.quotientAlgEquiv (K := R) x.1.asIdeal

/-- The quotient fiber `N(x)` carries its canonical `κ(x)`-module structure. -/
@[stacks 0GV8 "residue-field module structure on the closed-point fiber", instance]
noncomputable instance instModule
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) : Module κ(x) (N﹙x﹚) :=
  -- Local instance justification (defeq pin): use the standard quotient-module action before
  -- transporting scalars through the quotient-to-residue-field equivalence.
  let _ : Module (R ⧸ x.1.asIdeal) (N﹙x﹚) :=
    inferInstanceAs (Module (R ⧸ x.1.asIdeal) (N ⧸ x.1.asIdeal • (⊤ : Submodule R N)))
  let eκ := residueFieldAlgEquiv (R := R) x
  Module.compHom _ eκ.symm.toRingHom

/-- The original `R`-action and the residue-field action on `N(x)` form the canonical scalar
tower. -/
@[stacks 0GV8 "scalar tower on the closed-point fiber", instance]
noncomputable instance instIsScalarTower
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) : IsScalarTower R κ(x) (N﹙x﹚) := sorry
-- Proof strategy: expose the standard `R / x` quotient action, transport it through
-- `residueFieldAlgEquiv`, and apply `IsScalarTower.of_algebraMap_smul`; compatibility follows from
-- the algebra equivalence's `commutes` lemma.

/-- The quotient presentation `N(x)` is canonically linearly equivalent to the tensor fiber
`κ(x) ⊗[R] N`. -/
@[stacks 0GV8 "tensor description of the closed-point fiber"]
noncomputable def tensorEquiv
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) :
    κ(x) ⊗[R] N ≃ₗ[κ(x)] N﹙x﹚ :=
  let eκ := residueFieldAlgEquiv (R := R) x
  ((TensorProduct.congr eκ.symm.toLinearEquiv (LinearEquiv.refl R N)) ≪≫ₗ
      TensorProduct.quotTensorEquivQuotSMul N x.1.asIdeal).extendScalarsOfSurjective
    x.1.asIdeal.algebraMap_residueField_surjective

/-- A finite module has a finite-dimensional fiber at every closed point. -/
@[stacks 0GV8 "finite module has finite-dimensional closed-point fiber"]
theorem finiteDimensional_of_finite
    (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (x : closedPoints (PrimeSpectrum R)) : FiniteDimensional κ(x) (N﹙x﹚) := sorry
-- Proof strategy: use finiteness of scalar extension to make `κ(x) ⊗[R] N` finite-dimensional,
-- then transport the instance across `tensorEquiv N x`.

/-- Situation 15.128.1 (2), tag 0GV8: the fiber of a finitely presented module at a closed point
is finite-dimensional over the residue field. -/
@[stacks 0GV8 "finite-dimensional closed-point fiber"]
theorem finiteDimensional_of_finitePresentation
    (N : Type v) [AddCommGroup N] [Module R N] [Module.FinitePresentation R N]
    (x : closedPoints (PrimeSpectrum R)) : FiniteDimensional κ(x) (N﹙x﹚) := sorry
-- Proof strategy: obtain `Module.Finite R N` from finite presentation and apply
-- `finiteDimensional_of_finite N x`.

/-- Situation 15.128.1 (3), tag 0GV8: the image `s(x)` of `s : N` in the closed-point fiber. -/
@[stacks 0GV8 "section image in a closed-point fiber"]
abbrev mk {N : Type v} [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (s : N) : N﹙x﹚ :=
  Submodule.Quotient.mk s

scoped[ClosedPointFiber] notation:max s:max "⟮" x:max "⟯" =>
  Module.ClosedFiber.mk x s

end Module.ClosedFiber
