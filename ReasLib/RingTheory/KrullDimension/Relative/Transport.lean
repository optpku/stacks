module

public import ReasLib.RingTheory.KrullDimension.Relative

@[expose] public section

/-!
# Transport for relative dimension

This leaf compares relative dimension with raw fibers of prime spectra and transports it under
open spectral embeddings, algebra equivalences, and localizations away from one element.
-/

noncomputable section

universe u v w

section

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]

/-- Relative dimension at `q` is the local topological Krull dimension at the corresponding
point of the set-theoretic fiber over the contraction of `q`. -/
@[stacks 00QD "relative dimension as raw-fiber local dimension"]
theorem relativeDimensionAt_eq_topologicalKrullDimAt_fiberPoint (q : PrimeSpectrum S) :
    relativeDimensionAt R S q =
      topologicalKrullDimAt
        (⟨q, rfl⟩ : (PrimeSpectrum.comap (algebraMap R S) ⁻¹'
          {PrimeSpectrum.comap (algebraMap R S) q} : Set (PrimeSpectrum S))) := sorry

/-- Relative dimension at `q` can be viewed in the raw fiber over any explicitly named
contraction point equal to the contraction of `q`. -/
@[stacks 00QD "relative dimension in a named raw fiber"]
theorem relativeDimensionAt_eq_topologicalKrullDimAt_fiberPoint_of_comap_eq
    {p : PrimeSpectrum R} (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    relativeDimensionAt R S q =
      topologicalKrullDimAt
        (⟨q, hq⟩ : (PrimeSpectrum.comap (algebraMap R S) ⁻¹'
          {p} : Set (PrimeSpectrum S))) := sorry

/-- An open embedding induced by an `R`-algebra map preserves relative dimension after
contraction. The algebra-map compatibility is carried by `f`, rather than exposed as a separate
proof parameter. -/
@[stacks 00QD "relative dimension under open spectral embeddings"]
theorem relativeDimensionAt_comap_eq_of_isOpenEmbedding
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (hf : Topology.IsOpenEmbedding (PrimeSpectrum.comap f.toRingHom))
    (q : PrimeSpectrum B) :
    relativeDimensionAt R A (PrimeSpectrum.comap f.toRingHom q) = relativeDimensionAt R B q := sorry

/-- Relative dimension is invariant under an algebra equivalence of the target. -/
@[stacks 00QD "relative dimension under algebra equivalence"]
theorem relativeDimensionAt_eq_of_algEquiv
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (q : PrimeSpectrum B) :
    relativeDimensionAt R A (PrimeSpectrum.comap e.toRingHom q) = relativeDimensionAt R B q := sorry

/-- Localizing the target away from one element preserves relative dimension at corresponding
primes. -/
@[stacks 00QD "relative dimension under localization away"]
theorem relativeDimensionAt_localizationAway_comap (g : S)
    (qg : PrimeSpectrum (Localization.Away g)) :
    relativeDimensionAt R (Localization.Away g) qg =
      relativeDimensionAt R S
        (PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg) := sorry

/-- Pointwise relative-dimension bounds over a fixed base prime bound the Krull dimension of
the entire residue-field fiber over that prime. -/
@[stacks 00QD "fiber dimension from pointwise relative-dimension bounds"]
theorem ringKrullDim_fiber_le_of_forall_relativeDimensionAt_le
    (p : PrimeSpectrum R) (d : WithBot ℕ∞)
    (h : ∀ q : PrimeSpectrum S, PrimeSpectrum.comap (algebraMap R S) q = p →
      relativeDimensionAt R S q ≤ d) :
    ringKrullDim (p.asIdeal.Fiber S) ≤ d := sorry

namespace RelativeDimensionAtLELocus

/-- If the principal open `D(g)` lies in the locus where relative dimension is at most `d`, then
every residue-field fiber of `R → S_g` has Krull dimension at most `d`.

This is the localization bridge from pointwise relative-dimension bounds to whole-fiber bounds;
it has no finite-type or presentation hypothesis. -/
@[stacks 00QD "fiber dimension bound on a relative-dimension chart"]
theorem fiberKrullDim_localizationAway_le
    {A : Type v} [CommRing A] [Algebra R A] {d : ℕ} (g : A)
    (hbasic : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ⊆
      relativeDimensionAtLELocus R A d)
    (p : PrimeSpectrum R) :
    ringKrullDim (p.asIdeal.Fiber (Localization.Away g)) ≤ (d : WithBot ℕ∞) := sorry

end RelativeDimensionAtLELocus

end
