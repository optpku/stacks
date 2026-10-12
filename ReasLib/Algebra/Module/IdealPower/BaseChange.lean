/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.RingTheory.RingHom.Quotient
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change on ideal-power torsion

The canonical tensor unit `M → S ⊗[R] M` restricts from the `I`-primary component to the
`I.map σ`-primary component.  The map is explicit; only the membership proof is deferred.

@stack 05EC
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w

namespace Ideal.primaryComponent

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable (σ : R →+* S) (I : Ideal R)
variable (M : Type w) [AddCommGroup M] [Module R M]

/-- The tensor unit sends `I`-power-torsion elements to `I.map σ`-power-torsion elements. -/
@[stacks 05EC "tensor unit preserves ideal-power torsion"]
theorem baseChangeUnit_mem (x : I.primaryComponent M) :
    let _ : Algebra R S := σ.toAlgebra
    TensorProduct.mk R S M 1 x ∈
      (I.map σ).primaryComponent (S ⊗[R] M) := sorry

/-- The canonical tensor base-change unit restricted to the `I`-primary component. -/
@[stacks 05EC "base change on primary components"]
noncomputable def baseChangeUnit :
    let _ : Algebra R S := σ.toAlgebra
    I.primaryComponent M →ₗ[R]
      (((I.map σ).primaryComponent (S ⊗[R] M)).restrictScalars R) :=
  let _ : Algebra R S := σ.toAlgebra
  ((TensorProduct.mk R S M 1).domRestrict (I.primaryComponent M)).codRestrict
    (((I.map σ).primaryComponent (S ⊗[R] M)).restrictScalars R)
    (baseChangeUnit_mem σ I M)

/-- The restricted base-change unit is the pure tensor `x ↦ 1 ⊗ₜ[R] x`. -/
@[stacks 05EC "base-change unit formula"]
theorem baseChangeUnit_apply (x : I.primaryComponent M) :
    let _ : Algebra R S := σ.toAlgebra
    (baseChangeUnit σ I M x : S ⊗[R] M) = (1 : S) ⊗ₜ[R] (x : M) := sorry

/-- Lemma 15.90.3 (1) (05EC): for a flat map inducing an isomorphism
modulo a finitely generated ideal, the tensor unit is bijective on primary
components. -/
@[stacks 05EC "ideal-power torsion under flat base change"]
theorem baseChangeUnit_bijective (hI : I.FG) (hflat : σ.Flat)
    (hquot : Function.Bijective (σ.quotientByIdeal I)) :
    let _ : Algebra R S := σ.toAlgebra
    Function.Bijective (baseChangeUnit σ I M) := sorry

end Ideal.primaryComponent
