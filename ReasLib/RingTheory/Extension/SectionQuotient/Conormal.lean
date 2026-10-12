/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Extension.SectionQuotient
public import ReasLib.RingTheory.Kaehler.Quotient
import Mathlib.Tactic.CrossRefAttribute

/-!
# Conormal classes of cotangent-section quotients

The differential of every generator of a cotangent-section image ideal lies
in the range of the canonical quotient-linear conormal map. The statement is
independent of any chosen presentation of the extension.

@stack 04EF
-/

@[expose] public section

open scoped TensorProduct
open Algebra TensorProduct

noncomputable section

universe u v w

namespace Algebra.Extension.SectionQuotient

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- The differential class of each transported cotangent-section generator
lies in the range of the canonical quotient-linear conormal map. -/
@[stacks 04EF "cotangent-section generator differential in the conormal range"]
theorem generator_differential_mem_range {P : Extension A B}
    (l : P.CotangentSpace →ₗ[B] P.Cotangent) (x : P.CotangentSpace) :
    1 ⊗ₜ[P.infinitesimal.Ring]
        KaehlerDifferential.D R P.infinitesimal.Ring (generatorToInfinitesimal P l x) ∈
      LinearMap.range
        (KaehlerDifferential.Quotient.conormalToQuotient (R := R) (ideal P l)) := by
  let z : ideal P l := ⟨generatorToInfinitesimal P l x, generator_mem P l x⟩
  exact ⟨Ideal.toCotangent (ideal P l) z,
    KaehlerDifferential.Quotient.conormalToQuotient_toCotangent (ideal P l) z⟩

end Algebra.Extension.SectionQuotient
