/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.QuotientByIdeal.QuotientRing

/-!
# Spans in ideal quotients

This leaf records the canonical relation between an `R`-span in a module and
the corresponding span over `R ⧸ I`.  It keeps quotient-span reasoning
independent of any finite-family or localization argument.

@stack 0GLX
-/

@[expose] public section

universe u v

namespace Submodule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Restriction of scalars identifies the span of quotient classes with the image of the original
span under the canonical ideal-quotient map. -/
@[stacks 0GLX "span after quotient by an ideal"]
theorem restrictScalars_span_mkQ_eq_map_span (I : Ideal R) (s : Set M) :
    (Submodule.span (R ⧸ I) ((I • (⊤ : Submodule R M)).mkQ '' s)).restrictScalars R =
      Submodule.map (I • (⊤ : Submodule R M)).mkQ (Submodule.span R s) := sorry

/-- Membership in a span over `R ⧸ I` is equivalent to membership in the original span together
with the ideal multiple of the ambient module. -/
@[stacks 0GLX "quotient-span membership criterion"]
theorem mem_span_mkQ_iff_mem_span_sup_smul_top (I : Ideal R) (s : Set M) (m : M) :
    (I • (⊤ : Submodule R M)).mkQ m ∈
        Submodule.span (R ⧸ I) ((I • (⊤ : Submodule R M)).mkQ '' s) ↔
      m ∈ Submodule.span R s ⊔ I • (⊤ : Submodule R M) := sorry

end Submodule
