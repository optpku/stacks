module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Predicate
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Epi
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Source Comparison for Bounded-Above Resolutions

This file bridges the elementary source-facing replacement predicates to the canonical fixed
upper-bound left-resolution objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]
variable {P : ObjectProperty A} {a : ℤ} {K : CochainComplex A ℤ}

/-- Expose a canonical fixed-upper-bound left resolution as the source-facing bounded
quasi-isomorphism predicate. -/
@[stacks 05T7 "canonical upper resolution as source predicate"]
abbrev toBoundedQuasiIso (R : QuasiIsoFrom P a K) :
    CochainComplex.Minus.TermsIn.Bounded.QuasiIso
      P a K R.complex R.comparison where
  toBounded :=
    { strictlyLE := R.model.property.1
      term_mem := R.model.property.2 }
  quasiIso := R.hw

namespace Epi

/-- Expose a canonical epimorphic fixed-upper-bound left resolution as the source-facing
termwise-epimorphic bounded quasi-isomorphism predicate. -/
@[stacks 05T7 "canonical epimorphic upper resolution as source predicate"]
abbrev toBoundedQuasiIso [HasPushouts A] (R : QuasiIsoFrom.Epi P a K) :
    CochainComplex.Minus.TermsIn.Bounded.QuasiIso.Epi
      P a K R.complex R.comparison where
  toQuasiIso := R.toQuasiIsoFrom.toBoundedQuasiIso
  term_epi := R.comparison_epi_f

end Epi

end CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom

namespace CochainComplex.Minus.TermsIn

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]
variable {P : ObjectProperty A} {a : ℤ} {K Q : CochainComplex A ℤ} {α : Q ⟶ K}

namespace Bounded.QuasiIso

/-- Regard source-facing bounded replacement data as the canonical fixed-bound left
resolution. -/
@[stacks 05T7 "source predicate as canonical upper resolution"]
def toResolution (h : Bounded.QuasiIso P a K Q α) :
    CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom P a K :=
  CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom.mk h.toStrictlyLE α h.quasiIso

/-- The canonical resolution associated to source-facing data retains its bundled fixed-bound
model. -/
@[simp]
theorem toResolution_model (h : Bounded.QuasiIso P a K Q α) :
    h.toResolution.model = h.toStrictlyLE := sorry

/-- The canonical resolution associated to source-facing data retains its source complex. -/
@[simp]
theorem toResolution_complex (h : Bounded.QuasiIso P a K Q α) :
    h.toResolution.complex = Q := sorry

/-- The canonical resolution associated to source-facing data retains its comparison. -/
@[simp]
theorem toResolution_comparison (h : Bounded.QuasiIso P a K Q α) :
    h.toResolution.comparison = α := sorry

/-- Converting source-facing bounded quasi-isomorphism data to a resolution and back recovers
the original predicate. -/
@[simp]
theorem toResolution_toBoundedQuasiIso (h : Bounded.QuasiIso P a K Q α) :
    h.toResolution.toBoundedQuasiIso = h := sorry

end Bounded.QuasiIso

namespace Bounded.QuasiIso.Epi

/-- Regard source-facing termwise-epimorphic data as the canonical epimorphic fixed-bound left
resolution. -/
@[stacks 05T7 "source predicate as canonical epimorphic upper resolution"]
def toResolution (h : Bounded.QuasiIso.Epi P a K Q α) :
    CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom.Epi P a K :=
  CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom.Epi.mk
    h.toStrictlyLE α h.quasiIso
      (HomologicalComplex.epi_of_epi_f α h.term_epi)

/-- The canonical epimorphic resolution retains its bundled fixed-bound model. -/
@[simp]
theorem toResolution_model (h : Bounded.QuasiIso.Epi P a K Q α) :
    h.toResolution.model = h.toStrictlyLE := sorry

/-- The canonical epimorphic resolution retains the source complex. -/
@[simp]
theorem toResolution_complex (h : Bounded.QuasiIso.Epi P a K Q α) :
    h.toResolution.complex = Q := sorry

/-- The canonical epimorphic resolution retains the comparison. -/
@[simp]
theorem toResolution_comparison (h : Bounded.QuasiIso.Epi P a K Q α) :
    h.toResolution.comparison = α := sorry

/-- Converting source-facing epimorphic replacement data to a resolution and back recovers the
original predicate. -/
@[simp]
theorem toResolution_toBoundedQuasiIso [HasPushouts A]
    (h : Bounded.QuasiIso.Epi P a K Q α) :
    h.toResolution.toBoundedQuasiIso = h := sorry

end Bounded.QuasiIso.Epi

namespace Resolution

/-- Canonical fixed-upper-bound left resolutions are equivalent to the source-facing bounded
quasi-isomorphism data. -/
theorem nonempty_iff :
    Nonempty (CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom P a K) ↔
      ∃ (Q : CochainComplex A ℤ) (α : Q ⟶ K), Bounded.QuasiIso P a K Q α := sorry

/-- With pushouts, canonical epimorphic fixed-upper-bound left resolutions are equivalent to
the source-facing termwise-epimorphic data. -/
theorem nonempty_epi_iff [HasPushouts A] :
    Nonempty (CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom.Epi P a K) ↔
      ∃ (Q : CochainComplex A ℤ) (α : Q ⟶ K), Bounded.QuasiIso.Epi P a K Q α := sorry

end Resolution

end CochainComplex.Minus.TermsIn

namespace CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]
variable {P : ObjectProperty A} {a : ℤ} {K : CochainComplex A ℤ}

/-- Converting a fixed-bound left resolution to source-facing data and back recovers the
original resolution. -/
@[simp]
theorem toBoundedQuasiIso_toResolution (R : QuasiIsoFrom P a K) :
    R.toBoundedQuasiIso.toResolution = R := sorry

namespace Epi

/-- Converting an epimorphic fixed-bound left resolution to source-facing data and back
recovers the original resolution. -/
@[simp]
theorem toBoundedQuasiIso_toResolution [HasPushouts A] (R : QuasiIsoFrom.Epi P a K) :
    R.toBoundedQuasiIso.toResolution = R := sorry

end Epi

end CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom


