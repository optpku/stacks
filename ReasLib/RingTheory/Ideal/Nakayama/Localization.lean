module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.LocalizedModule.Finite
public import ReasLib.LinearAlgebra.QuotientByIdeal.Span
public import ReasLib.RingTheory.Ideal.Nakayama.Basic

/-!
# Nakayama localization criteria

This leaf owns the finite-module denominator statement behind localization
away from an element of `S + I`.  The primary interface is `R`-linear and
uses the canonical ideal quotient; quotient-ring span and linear-map forms
are companion views for source-facing and downstream applications.

@stack 0GLX
-/

@[expose] public section

universe u v w

open scoped Pointwise

namespace Submodule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- If the ideal quotient of a submodule of a finite ambient module is generated after localizing
at `S`, some element of `S + I` clears the generation denominator and makes the submodule generate
after the corresponding principal localization. -/
@[stacks 0GLX "finite quotient generation and localization"]
theorem exists_mem_add_ideal_and_smul_top_le_of_quotient_localized_eq_top
    (S : Submonoid R) (I : Ideal R) [Module.Finite R M] (N : Submodule R M)
    (hgen : (N.map (I • (⊤ : Submodule R M)).mkQ).localized S = ⊤) :
    ∃ f : R, f ∈ ((S : Set R) + (I : Set R)) ∧
      f • (⊤ : Submodule R M) ≤ N ∧ N.localized (Submonoid.powers f) = ⊤ := sorry

/-- The localization conclusion of the finite quotient-generation criterion, without exposing the
intermediate clearing-scalar inclusion. -/
@[stacks 0GLX "finite quotient generation localized top"]
theorem exists_mem_add_ideal_and_localized_eq_top_of_quotient_localized_eq_top
    (S : Submonoid R) (I : Ideal R) [Module.Finite R M] (N : Submodule R M)
    (hgen : (N.map (I • (⊤ : Submodule R M)).mkQ).localized S = ⊤) :
    ∃ f : R, f ∈ ((S : Set R) + (I : Set R)) ∧ N.localized (Submonoid.powers f) = ⊤ := sorry

/-- The quotient-ring span view of the finite localization criterion for an arbitrary generating
set.  The unrestricted `Set M` form is the reusable owner of finite-family source statements. -/
@[stacks 0GLX "quotient-span localization criterion"]
theorem exists_mem_add_ideal_and_span_localized_eq_top_of_quotient_span_localized_eq_top
    (S : Submonoid R) (I : Ideal R) [Module.Finite R M] (s : Set M)
    (hgen :
      (Submodule.span (R ⧸ I)
        ((I • (⊤ : Submodule R M)).mkQ '' s)).localized
          (Algebra.algebraMapSubmonoid (R ⧸ I) S) = ⊤) :
    ∃ f : R, f ∈ ((S : Set R) + (I : Set R)) ∧
      (Submodule.span R s).localized (Submonoid.powers f) = ⊤ := sorry

end Submodule

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- A quotient map that is surjective after localizing at `S` becomes surjective after localizing
at a principal element belonging to `S + I`. -/
@[stacks 0GLX "localized quotient-map surjectivity criterion"]
theorem exists_mem_add_ideal_and_localizedMap_surjective_of_quotientMap_localized_surjective
    (S : Submonoid R) (I : Ideal R) (g : N →ₗ[R] M) [Module.Finite R M]
    (hgen :
      Function.Surjective
        (LocalizedModule.map S (g.quotientMapByIdeal I))) :
    ∃ f : R, f ∈ ((S : Set R) + (I : Set R)) ∧
      Function.Surjective (LocalizedModule.map (Submonoid.powers f) g) := sorry

end LinearMap
