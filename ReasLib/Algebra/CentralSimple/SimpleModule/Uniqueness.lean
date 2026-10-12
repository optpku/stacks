/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.CentralSimple.SimpleModule.Existence
public import ReasLib.Algebra.Module.Matrix.Simple
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin

@[expose] public section

/-! # Uniqueness of simple modules

This file establishes that any two simple left modules over a simple Artinian ring are
isomorphic.  The standard matrix-module simplicity fact is owned separately by
`ReasLib.Algebra.Module.Matrix.Simple`.
-/

universe u v w w'

namespace IsSimpleModule

section

open LinearMap

variable {k : Type u} {A : Type v}
variable [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]

variable {M : Type w} {N : Type w'}
variable [AddCommGroup M] [Module A M]
variable [AddCommGroup N] [Module A N]

/-- Any two simple left `A`-modules are isomorphic. -/
@[stacks 074E]
theorem nonempty_linearEquiv
    {A : Type v} [Ring A] [IsSimpleRing A] [IsArtinianRing A] {M : Type w} {N : Type w'}
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [IsSimpleModule A M] [IsSimpleModule A N] :
    Nonempty (M ≃ₗ[A] N) := by
  have hA : IsIsotypic A A := IsSimpleRing.isIsotypic A A
  have ⟨I, ⟨eM⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule A M
  have ⟨J, ⟨eN⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule A N
  let _ : IsSimpleModule A I := eM.isSimpleModule_iff.mp inferInstance
  let _ : IsSimpleModule A J := eN.isSimpleModule_iff.mp inferInstance
  have hJI : Nonempty (J ≃ₗ[A] I) := hA I J
  exact ⟨eM.trans hJI.some.symm |>.trans eN.symm⟩

end

end IsSimpleModule

end
