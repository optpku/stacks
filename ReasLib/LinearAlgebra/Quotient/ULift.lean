module

public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.Quotient.ULift

@[expose] public section

/-!
# Universe lifts of quotients by ideal multiples

This leaf packages the quotient-module comparison induced by `ULift.moduleEquiv`
and the corresponding flatness transport.  It keeps the equivalence concrete,
so consumers do not choose it through a `Nonempty` witness.
-/

universe u v w

namespace Ideal

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]

/-- The `ULift` module equivalence maps the quotient denominator `J • ⊤` onto the corresponding
denominator of the original module. -/
theorem map_uliftModuleEquiv_smul_top (J : Ideal A) :
    Submodule.map (ULift.moduleEquiv : ULift.{u} M ≃ₗ[A] M).toLinearMap
        (J • (⊤ : Submodule A (ULift.{u} M))) =
      J • (⊤ : Submodule A M) := by
  simpa [Submodule.map_smul'']

/-- Quotienting `ULift M` by `J • ⊤` is canonically equivalent, over `A ⧸ J`, to quotienting
`M` by the same ideal multiple. -/
@[stacks 051I]
noncomputable def uliftModuleQuotientEquiv (J : Ideal A) :
    (ULift.{u} M ⧸ (J • (⊤ : Submodule A (ULift.{u} M)))) ≃ₗ[A ⧸ J]
      M ⧸ (J • (⊤ : Submodule A M)) :=
  (Submodule.Quotient.equiv
    (J • (⊤ : Submodule A (ULift.{u} M)))
    (J • (⊤ : Submodule A M))
    (ULift.moduleEquiv : ULift.{u} M ≃ₗ[A] M)
    (map_uliftModuleEquiv_smul_top J)).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective

end Ideal

namespace Module.Flat

variable {A : Type u} [CommRing A]
variable {M : Type w} [AddCommGroup M] [Module A M]

/-- Flatness of a quotient module is preserved after lifting the ring and module to a common
universe and mapping the quotient ideal. -/
@[stacks 051I]
theorem uliftQuotient (J : Ideal A)
    (hflat : Module.Flat (A ⧸ J) (M ⧸ (J • (⊤ : Submodule A M)))) :
    Module.Flat (ULift.{w} A ⧸ J.map (algebraMap A (ULift.{w} A)))
      (ULift.{u} M ⧸
        (J.map (algebraMap A (ULift.{w} A)) •
          (⊤ : Submodule (ULift.{w} A) (ULift.{u} M)))) := sorry

end Module.Flat
