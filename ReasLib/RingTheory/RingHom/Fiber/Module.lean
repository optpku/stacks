/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Prime.Module
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.Module.Support.BaseChange
public import ReasLib.RingTheory.RingHom.Fiber.ResidueFieldAtPrime

/-!
# Modules Over Residue-Field Fibers

This leaf owns the standard comparison between a module tensored with a
residue-field fiber and the corresponding residue-field tensor of the module,
along with the induced support-point descent.

@stack 05GC
@stack 080T
@stack 00UV
-/

@[expose] public section

noncomputable section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w

namespace Ideal.Fiber

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Tensoring an `S`-module with the fiber over `p` is canonically the same
as tensoring the module over `R` with the residue field at `p`. -/
@[stacks 05GC "fiber-module tensor comparison"]
noncomputable def tensorModuleEquiv (p : PrimeSpectrum R) :
    (p.asIdeal.Fiber S) ⊗[S] M ≃ₗ[S] M ⊗[R] p.asIdeal.ResidueField :=
  TensorProduct.comm S (p.asIdeal.Fiber S) M ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S M)
      (Algebra.TensorProduct.commRight R S p.asIdeal.ResidueField).symm.toLinearEquiv
      ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M p.asIdeal.ResidueField

/-- The canonical fiber-module comparison preserves nontriviality. -/
@[stacks 05GC "fiber-module tensor comparison"]
theorem nontrivial_tensorModule_iff (p : PrimeSpectrum R) :
    Nontrivial ((p.asIdeal.Fiber S) ⊗[S] M) ↔
      Nontrivial (M ⊗[R] p.asIdeal.ResidueField) := sorry

/-- The target-spectrum point corresponding to a prime `q` of the residue-field fiber over `p`. -/
@[stacks 080T "support point over a fiber prime"]
noncomputable def supportPoint (p : PrimeSpectrum R)
    (q : PrimeSpectrum (p.asIdeal.Fiber S)) : PrimeSpectrum S :=
  ((PrimeSpectrum.preimageEquivFiber R S p).symm q).1

/-- A support point of the fiber module maps to a support point of the original module. -/
@[stacks 080T "support point over a fiber prime"]
theorem supportPoint_mem_support [Module.Finite S M]
    (p : PrimeSpectrum R) (q : PrimeSpectrum (p.asIdeal.Fiber S))
    (hq : q ∈ Module.support (p.asIdeal.Fiber S) ((p.asIdeal.Fiber S) ⊗[S] M)) :
    supportPoint p q ∈ Module.support S M := sorry

/-- The support point associated with a fiber prime lies over the selected base prime. -/
@[stacks 080T "support point over a fiber prime", simp]
theorem supportPoint_comap (p : PrimeSpectrum R)
    (q : PrimeSpectrum (p.asIdeal.Fiber S)) :
    PrimeSpectrum.comap (algebraMap R S) (supportPoint p q) = p := sorry

end Ideal.Fiber

namespace PrimeSpectrum.Fiber

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Taking the residue fiber at the canonical prime after base change to a
base residue-field fiber is canonically the same as taking the original
module fiber at the target point. -/
@[stacks 00UV "module fiber after residue-field base change"]
noncomputable def baseChangeFiber (q : PrimeSpectrum S) :
    (fiberPrimeAt R S q).asIdeal.Fiber
        ((q.asIdeal.under R).Fiber S ⊗[S] M) ≃ₗ[S]
      q.asIdeal.Fiber M :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange S
      ((q.asIdeal.under R).Fiber S) ((q.asIdeal.under R).Fiber S)
      (fiberPrimeAt R S q).asIdeal.ResidueField M).restrictScalars S ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr
      (fiberPrimeAt_residueFieldAlgEquiv (R := R) (S := S) q).toLinearEquiv
      (LinearEquiv.refl S M)

end PrimeSpectrum.Fiber
