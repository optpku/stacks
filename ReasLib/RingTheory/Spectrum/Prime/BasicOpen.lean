module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Principal basic opens

This leaf records reusable set-level and bundled-open facts relating principal
basic opens to zero loci and units.  It uses the canonical `PrimeSpectrum`
vocabulary, so downstream files do not need chapter-local `D` and `V`
notation.
@stack 00E0
@stack 04MG
-/

universe u v

namespace PrimeSpectrum

variable {R : Type u} [CommSemiring R]

/-- The principal nonmembership subsets of a prime spectrum form a basis for
the Zariski topology of every commutative ring. -/
theorem isTopologicalBasis_notMem :
    ∀ {A : Type u} [CommRing A], TopologicalSpace.IsTopologicalBasis
      (Set.range fun f : A => {p : PrimeSpectrum A | f ∉ p.asIdeal}) := sorry

/-- A point outside a zero locus lies in a principal basic open defined by an
element of the defining set, and that basic open is disjoint from the zero
locus. -/
@[stacks 00E0 "basic open disjoint from a zero locus"]
theorem exists_basicOpen_disjoint_zeroLocus_of_not_mem
    (T : Set R) (p : PrimeSpectrum R) (hp : p ∉ zeroLocus T) :
    ∃ f ∈ T, p ∈ basicOpen f ∧
      Disjoint (basicOpen f : Set (PrimeSpectrum R)) (zeroLocus T) := by
  rw [PrimeSpectrum.mem_zeroLocus] at hp
  obtain ⟨f, hfT, hfp⟩ := Set.not_subset.mp hp
  refine ⟨f, hfT, hfp, Set.disjoint_left.2 ?_⟩
  intro q hqf hqT
  exact hqf ((PrimeSpectrum.mem_zeroLocus q T).mp hqT hfT)

/-- The union of the principal basic opens defined by a family is the
complement of the zero locus of its range. -/
@[stacks 00E0 "union of principal basic opens"]
theorem iUnion_basicOpen_eq_compl_zeroLocus_range
    {ι : Sort v} (f : ι → R) :
    (⋃ i, (basicOpen (f i) : Set (PrimeSpectrum R))) =
      (zeroLocus (Set.range f))ᶜ := by
  classical
  ext p
  simp [PrimeSpectrum.mem_zeroLocus, Set.range_subset_iff]

/-- A principal basic open is the whole prime spectrum exactly when its
defining element is a unit. -/
@[stacks 00E0 "principal basic open is top"]
theorem basicOpen_eq_top_iff (f : R) :
    basicOpen f = ⊤ ↔ IsUnit f := by
  classical
  simpa using
    (PrimeSpectrum.iSup_basicOpen_eq_top_iff (R := R) (f := fun _ : Unit => f))

/-- Multiplying the defining element by a unit does not change its principal
basic open. -/
@[stacks 00E0 "unit multiple of a principal basic open"]
theorem basicOpen_unit_mul (u : Rˣ) (f : R) :
    basicOpen ((u : R) * f) = basicOpen f := by
  rw [basicOpen_mul]
  have hu : basicOpen (u : R) = ⊤ :=
    (basicOpen_eq_top_iff (u : R)).2 u.isUnit
  simp [hu]

/-- If every principal basic open is closed, then every compact open subset of the prime
spectrum is closed.  This is the spectrum-specific bridge from the basic-open basis to the
canonical spectral-space separation criteria. -/
@[stacks 04MG "closed compact opens from principal basic opens"]
theorem isClosed_compactOpen_of_basicOpen
    (hbasic : ∀ f : R, IsClosed ((basicOpen f : Set (PrimeSpectrum R))))
    {U : Set (PrimeSpectrum R)} (hU : IsOpen U) (hUcompact : IsCompact U) :
    IsClosed U := by
  obtain ⟨s, hs, hUs⟩ :=
    eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open
      (fun f : R => (basicOpen f : Set (PrimeSpectrum R)))
      PrimeSpectrum.isTopologicalBasis_basic_opens U hUcompact hU
  rw [hUs]
  exact hs.isClosed_biUnion fun f _ => hbasic f

end PrimeSpectrum
