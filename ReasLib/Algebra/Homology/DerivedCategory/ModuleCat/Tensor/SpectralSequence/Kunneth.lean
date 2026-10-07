module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.SpectralSequence
public import ReasLib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Tactic.CrossRefAttribute

/-!
# The bounded Künneth spectral sequence

This leaf records the bounded spectral sequence whose page-two entries are sums of Tor groups of
the cohomology modules of two bounded derived objects.  Convergence uses the canonical
filtered-complex convergence predicate.

@stack 0H7Z
-/

@[expose] public section

open CategoryTheory.Limits
open scoped BigOperators DerivedTensorProduct ZeroObject

noncomputable section

universe u

namespace CategoryTheory

variable {R : Type u} [CommRing R]

local notation "ModR" => ModuleCat R
local notation "DbModR" => DerivedCategory.Bounded ModR
local notation "H" => DerivedCategory.homologyFunctor ModR

/-- The abutment entry `H^n(K ⊗[R]^L L)` of the bounded Künneth spectral sequence. -/
@[stacks 0H7Z "abutment"]
abbrev boundedDerivedTensorCohomology
    (K L : DbModR) (n : ℤ) : ModR :=
  (H n).obj (K.obj ⊗[R]^L L.obj)

/-- The page-two entry
`⨁ i, Tor_(-p)^R(H^i(K), H^(q-i)(L))`, with zero entries for `p > 0`. -/
@[stacks 0H7Z "page-two entries"]
abbrev kunnethDerivedTensorPageTwo
    (K L : DbModR) (p q : ℤ) : ModR :=
  if _ : p ≤ 0 then
    ∐ fun i : ℤ ↦
      (((Tor ModR (Int.toNat (-p))).obj ((H i).obj K.obj)).obj
        ((H (q - i)).obj L.obj))
  else
    (0 : ModR)

/-- Convergence to derived tensor cohomology means convergence from a filtered complex whose
underlying cohomology identifies with the displayed abutment. -/
@[stacks 0H7Z "convergence to derived tensor cohomology"]
def ConvergesToDerivedTensorCohomology
    (E : CohomologicalSpectralSequence ModR 0) (K L : DbModR) : Prop :=
  ∃ F : FilteredComplex ModR,
    FilteredComplex.Cohomology.Convergence.Converges F E ∧
      ∀ n : ℤ,
        Nonempty (F.underlying.homology n ≅ boundedDerivedTensorCohomology K L n)

namespace ConvergesToDerivedTensorCohomology

/-- The filtered-complex specification of convergence to bounded derived tensor cohomology. -/
theorem spec
    {E : CohomologicalSpectralSequence ModR 0} {K L : DbModR} :
    ConvergesToDerivedTensorCohomology E K L ↔
      ∃ F : FilteredComplex ModR,
        FilteredComplex.Cohomology.Convergence.Converges F E ∧
          ∀ n : ℤ,
            Nonempty (F.underlying.homology n ≅ boundedDerivedTensorCohomology K L n) := sorry

end ConvergesToDerivedTensorCohomology

/-- A bounded Künneth spectral sequence is bounded, has the prescribed Tor page-two entries,
and converges to the cohomology of the derived tensor product. -/
@[stacks 0H7Z "bounded Künneth spectral-sequence specification"]
def IsKunnethDerivedTensorSpectralSequence
    (E : CohomologicalSpectralSequence ModR 0) (K L : DbModR) : Prop :=
  CohomologicalSpectralSequence.IsBounded E ∧
    (∀ p q : ℤ,
      Nonempty ((E.page 2).X (p, q) ≅ kunnethDerivedTensorPageTwo K L p q)) ∧
    ConvergesToDerivedTensorCohomology E K L

namespace IsKunnethDerivedTensorSpectralSequence

/-- The boundedness, page-two, and convergence clauses of a bounded Künneth spectral sequence. -/
theorem spec
    {E : CohomologicalSpectralSequence ModR 0} {K L : DbModR} :
    IsKunnethDerivedTensorSpectralSequence E K L ↔
      CohomologicalSpectralSequence.IsBounded E ∧
        (∀ p q : ℤ,
          Nonempty ((E.page 2).X (p, q) ≅ kunnethDerivedTensorPageTwo K L p q)) ∧
        ConvergesToDerivedTensorCohomology E K L := sorry

/-- A bounded Künneth spectral sequence is bounded. -/
theorem isBounded
    {E : CohomologicalSpectralSequence ModR 0} {K L : DbModR}
    (h : IsKunnethDerivedTensorSpectralSequence E K L) :
    CohomologicalSpectralSequence.IsBounded E := sorry

/-- The page-two entries of a bounded Künneth spectral sequence have the displayed Tor form. -/
theorem pageTwoIso
    {E : CohomologicalSpectralSequence ModR 0} {K L : DbModR}
    (h : IsKunnethDerivedTensorSpectralSequence E K L) (p q : ℤ) :
    Nonempty ((E.page 2).X (p, q) ≅ kunnethDerivedTensorPageTwo K L p q) := sorry

/-- A bounded Künneth spectral sequence converges to derived tensor cohomology. -/
theorem converges
    {E : CohomologicalSpectralSequence ModR 0} {K L : DbModR}
    (h : IsKunnethDerivedTensorSpectralSequence E K L) :
    ConvergesToDerivedTensorCohomology E K L := sorry

end IsKunnethDerivedTensorSpectralSequence

/-- Lemma 15.64.4 (Künneth Spectral Sequence): two bounded derived modules admit a bounded
cohomological spectral sequence with page two
`⨁ i, Tor_(-p)^R(H^i(K), H^(q-i)(L))` converging to `H^(p+q)(K ⊗[R]^L L)`. -/
@[stacks 0H7Z]
theorem exists_kunnethDerivedTensorSpectralSequence
    (K L : DbModR) :
    ∃ E : CohomologicalSpectralSequence ModR 0,
      IsKunnethDerivedTensorSpectralSequence E K L := sorry

end CategoryTheory
