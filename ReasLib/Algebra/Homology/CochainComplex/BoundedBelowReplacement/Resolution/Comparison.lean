/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Predicate
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Mono
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Source Comparison for Bounded-Below Resolutions

This file bridges the elementary source-facing replacement predicates to the canonical fixed
lower-bound right-resolution objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]
variable {P : ObjectProperty A} {a : ℤ} {K : CochainComplex A ℤ}

/-- Expose a canonical fixed-lower-bound right resolution as the source-facing bounded
quasi-isomorphism predicate. -/
@[stacks 05T6 "canonical lower resolution as source predicate"]
abbrev toBoundedQuasiIso (R : QuasiIsoTo P a K) :
    CochainComplex.Plus.TermsIn.Bounded.QuasiIso
      P a K R.complex R.comparison where
  toBounded :=
    { strictlyGE := R.model.property.1
      term_mem := R.model.property.2 }
  quasiIso := R.hw

namespace Mono

/-- Expose a canonical monomorphic fixed-lower-bound right resolution as the source-facing
termwise-monomorphic bounded quasi-isomorphism predicate. -/
@[stacks 05T6 "canonical monomorphic lower resolution as source predicate"]
abbrev toBoundedQuasiIso [HasPullbacks A] (R : QuasiIsoTo.Mono P a K) :
    CochainComplex.Plus.TermsIn.Bounded.QuasiIso.Mono
      P a K R.complex R.comparison where
  toQuasiIso := R.toQuasiIsoTo.toBoundedQuasiIso
  term_mono := R.comparison_mono_f

end Mono

end CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo

namespace CochainComplex.Plus.TermsIn

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]
variable {P : ObjectProperty A} {a : ℤ} {K I : CochainComplex A ℤ} {α : K ⟶ I}

namespace Bounded.QuasiIso

/-- Regard source-facing bounded replacement data as the canonical fixed-bound right
resolution. -/
@[stacks 05T6 "source predicate as canonical lower resolution"]
def toResolution (h : Bounded.QuasiIso P a K I α) :
    CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo P a K :=
  CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo.mk h.toStrictlyGE α h.quasiIso

/-- The canonical resolution associated to source-facing data retains its bundled fixed-bound
model. -/
@[simp]
theorem toResolution_model (h : Bounded.QuasiIso P a K I α) :
    h.toResolution.model = h.toStrictlyGE := sorry

/-- The canonical resolution associated to source-facing data retains its target complex. -/
@[simp]
theorem toResolution_complex (h : Bounded.QuasiIso P a K I α) :
    h.toResolution.complex = I := sorry

/-- The canonical resolution associated to source-facing data retains its comparison. -/
@[simp]
theorem toResolution_comparison (h : Bounded.QuasiIso P a K I α) :
    h.toResolution.comparison = α := sorry

/-- Converting source-facing bounded quasi-isomorphism data to a resolution and back recovers
the original predicate. -/
@[simp]
theorem toResolution_toBoundedQuasiIso (h : Bounded.QuasiIso P a K I α) :
    h.toResolution.toBoundedQuasiIso = h := sorry

end Bounded.QuasiIso

namespace Bounded.QuasiIso.Mono

/-- Regard source-facing termwise-monomorphic data as the canonical monomorphic fixed-bound
right resolution. -/
@[stacks 05T6 "source predicate as canonical monomorphic lower resolution"]
def toResolution (h : Bounded.QuasiIso.Mono P a K I α) :
    CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo.Mono P a K :=
  CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo.Mono.mk
    h.toStrictlyGE α h.quasiIso
      (HomologicalComplex.mono_of_mono_f α h.term_mono)

/-- The canonical monomorphic resolution retains its bundled fixed-bound model. -/
@[simp]
theorem toResolution_model (h : Bounded.QuasiIso.Mono P a K I α) :
    h.toResolution.model = h.toStrictlyGE := sorry

/-- The canonical monomorphic resolution retains the target complex. -/
@[simp]
theorem toResolution_complex (h : Bounded.QuasiIso.Mono P a K I α) :
    h.toResolution.complex = I := sorry

/-- The canonical monomorphic resolution retains the comparison. -/
@[simp]
theorem toResolution_comparison (h : Bounded.QuasiIso.Mono P a K I α) :
    h.toResolution.comparison = α := sorry

/-- Converting source-facing monomorphic replacement data to a resolution and back recovers
the original predicate. -/
@[simp]
theorem toResolution_toBoundedQuasiIso [HasPullbacks A]
    (h : Bounded.QuasiIso.Mono P a K I α) :
    h.toResolution.toBoundedQuasiIso = h := sorry

end Bounded.QuasiIso.Mono

namespace Resolution

/-- Canonical fixed-lower-bound right resolutions are equivalent to the source-facing bounded
quasi-isomorphism data. -/
theorem nonempty_iff :
    Nonempty (CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo P a K) ↔
      ∃ (I : CochainComplex A ℤ) (α : K ⟶ I), Bounded.QuasiIso P a K I α := sorry

/-- With pullbacks, canonical monomorphic fixed-lower-bound right resolutions are equivalent
to the source-facing termwise-monomorphic data. -/
theorem nonempty_mono_iff [HasPullbacks A] :
    Nonempty (CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo.Mono P a K) ↔
      ∃ (I : CochainComplex A ℤ) (α : K ⟶ I), Bounded.QuasiIso.Mono P a K I α := sorry

end Resolution

end CochainComplex.Plus.TermsIn

namespace CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]
variable {P : ObjectProperty A} {a : ℤ} {K : CochainComplex A ℤ}

/-- Converting a fixed-bound right resolution to source-facing data and back recovers the
original resolution. -/
@[simp]
theorem toBoundedQuasiIso_toResolution (R : QuasiIsoTo P a K) :
    R.toBoundedQuasiIso.toResolution = R := sorry

namespace Mono

/-- Converting a monomorphic fixed-bound right resolution to source-facing data and back
recovers the original resolution. -/
@[simp]
theorem toBoundedQuasiIso_toResolution [HasPullbacks A] (R : QuasiIsoTo.Mono P a K) :
    R.toBoundedQuasiIso.toResolution = R := sorry

end Mono

end CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo


