module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Module
public import ReasLib.Algebra.Module.FinitePresentation.Localization
public import ReasLib.Algebra.Module.LocalizedModule.Quotient
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite modules after quotient and localization

@stack 05N5

This leaf owns the two approximation statements used by the quotient-localization
construction.  A finite (respectively finitely presented) module over the
localization of `R ⧸ I` is represented by a finite (respectively finitely
presented) `R`-module after quotienting by `I • ⊤` and localizing.  The
presentation choices used to prove the statements are intentionally hidden
from consumers.
-/

@[expose] public section

universe u v

namespace Module.Finite

variable {R : Type u} [CommRing R]
variable (I : Ideal R) (S : Submonoid R)

-- Local declaration justification (source-local notation): these aliases keep the quotient and
-- localized coefficient rings readable in the two source-facing approximation statements.
local notation "Sbar" => Algebra.algebraMapSubmonoid (R ⧸ I) S
local notation "R'" => Localization Sbar

/-- Tag `05N5` (finite clause): every finite module over
`Localization (Algebra.algebraMapSubmonoid (R ⧸ I) S)` is the localization of
the quotient by `I • ⊤` of a finite `R`-module.  The equivalence is exposed as
the only witness needed by downstream consumers; no finite presentation
matrix or denominator-clearing data is part of the owner API. -/
@[stacks 05N5 "finite quotient-localized module model"]
theorem exists_quotient_localized_model
    (M' : Type v) [AddCommGroup M'] [Module R' M'] [Module.Finite R' M'] :
    ∃ (M : Type v) (_ : AddCommGroup M) (_ : Module R M) (_ : Module.Finite R M),
      Nonempty
        (LocalizedModule Sbar (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R'] M') := sorry

end Module.Finite

namespace Module.FinitePresentation

variable {R : Type u} [CommRing R]
variable (I : Ideal R) (S : Submonoid R)

-- Local declaration justification (source-local notation): the same aliases expose the concrete
-- coefficient ring named in the finitely-presented clause without creating global notation.
local notation "Sbar" => Algebra.algebraMapSubmonoid (R ⧸ I) S
local notation "R'" => Localization Sbar

/-- Tag `05N5` (finite-presentation clause): every finitely presented module
over `Localization (Algebra.algebraMapSubmonoid (R ⧸ I) S)` is the localization
of the quotient by `I • ⊤` of a finitely presented `R`-module.  The owner only
returns the source module and its localized linear equivalence, leaving the
finite-free presentation used in the proof private. -/
@[stacks 05N5 "finitely presented quotient-localized module model"]
theorem exists_quotient_localized_model
    (M' : Type v) [AddCommGroup M'] [Module R' M']
    [Module.FinitePresentation R' M'] :
    ∃ (M : Type (max u v)) (_ : AddCommGroup M) (_ : Module R M)
      (_ : Module.FinitePresentation R M),
      Nonempty
        (LocalizedModule Sbar (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R'] M') := sorry

end Module.FinitePresentation
