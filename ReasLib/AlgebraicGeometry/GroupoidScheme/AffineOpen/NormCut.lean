module

public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Invariant
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# The opens and sections in the invariant affine neighbourhood construction

The construction of Stacks 03JE first removes every orbit meeting the complement of an affine
open, then chooses one principal open containing the finite orbit. These two steps are explicit
here. An explicitly supplied determinantal norm gives the subsequent norm section and open.
The construction of that norm and an affine presentation of its nonvanishing open are separate
inputs to the full invariant affine neighbourhood producer.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme.AffineOpenConstruction

/-- A finite subset of an affine spectrum inside an open has a common principal neighbourhood
inside that open. The element is supplied by the proved prime-avoidance theorem. -/
theorem exists_basicOpen_contains_finite {A : Type u} [CommRing A]
    (E : Set (PrimeSpectrum A)) (hE : E.Finite) (V : Opens (PrimeSpectrum A))
    (hEV : E ⊆ V) :
    ∃ f : A, E ⊆ PrimeSpectrum.basicOpen f ∧ PrimeSpectrum.basicOpen f ≤ V := by
  classical
  let I : Ideal A := PrimeSpectrum.vanishingIdeal (V : Set (PrimeSpectrum A))ᶜ
  let primes : Set (Ideal A) := PrimeSpectrum.asIdeal '' E
  have hprimes : primes.Finite := hE.image PrimeSpectrum.asIdeal
  have havoid : ¬ (I : Set A) ⊆ ⋃ p ∈ primes, (p : Set A) := by
    intro h
    obtain ⟨p, hp, hIp⟩ :=
      (Ideal.subset_union_prime_finite hprimes (⊤ : Ideal A) ⊤ (by
        rintro p ⟨x, hx, rfl⟩ _ _
        exact x.isPrime)).mp h
    obtain ⟨x, hx, rfl⟩ := hp
    have hxI : x ∈ PrimeSpectrum.zeroLocus (I : Set A) := hIp
    rw [show PrimeSpectrum.zeroLocus (I : Set A) = (V : Set (PrimeSpectrum A))ᶜ by
      exact (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure _).trans
        V.isOpen.isClosed_compl.closure_eq] at hxI
    exact hxI (hEV hx)
  obtain ⟨f, hfI, hfprimes⟩ := Set.not_subset.mp havoid
  refine ⟨f, ?_, ?_⟩
  · intro x hx
    change f ∉ x.asIdeal
    intro hfx
    exact hfprimes (Set.mem_iUnion₂.mpr ⟨x.asIdeal, ⟨x, hx, rfl⟩, hfx⟩)
  · intro x hx
    by_contra hxV
    exact hx ((PrimeSpectrum.mem_vanishingIdeal _ _).mp hfI x hxV)

/-- The common principal-neighbourhood construction on an affine open of a scheme. -/
theorem exists_affine_basicOpen_contains_finite {X : Scheme.{u}} (W : X.affineOpens)
    (E : Set X) (hE : E.Finite) (V : X.Opens) (hEW : E ⊆ W) (hEV : E ⊆ V) :
    ∃ f : Γ(X, W), E ⊆ X.basicOpen f ∧ X.basicOpen f ≤ V := by
  let points : Set (PrimeSpectrum Γ(X, W)) := W.2.fromSpec ⁻¹' E
  have hpoints : points.Finite := hE.preimage W.2.fromSpec.injective.injOn
  obtain ⟨f, hf, hfV⟩ := exists_basicOpen_contains_finite points hpoints
    (W.2.fromSpec ⁻¹ᵁ V) (fun x hx ↦ hEV hx)
  refine ⟨f, ?_, ?_⟩
  · intro x hx
    let p := W.2.primeIdealOf ⟨x, hEW hx⟩
    have hp : W.2.fromSpec p = x := W.2.fromSpec_primeIdealOf _
    have hpf : p ∈ PrimeSpectrum.basicOpen f := hf (by simpa [points, hp] using hx)
    rw [← W.2.fromSpec_preimage_basicOpen f] at hpf
    change W.2.fromSpec p ∈ X.basicOpen f at hpf
    rw [hp] at hpf
    exact hpf
  · rw [← W.2.fromSpec_image_basicOpen f]
    exact (W.2.fromSpec.image_mono hfV).trans (W.2.fromSpec.image_preimage_le V)

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- The largest invariant open contained in `W`, obtained by removing every orbit meeting
its complement. Its underlying subset is the actual complement of the saturation. -/
def invariantInterior [IsFinite G.t.left] (W : G.U.left.Opens) : G.U.left.Opens :=
  ⟨(G.t.left '' (G.s.left ⁻¹' (W : Set G.U.left)ᶜ))ᶜ,
    (G.t.left.isClosedMap _ (W.isOpen.isClosed_compl.preimage G.s.left.continuous)).isOpen_compl⟩

/-- The explicit point condition defining the invariant interior. -/
theorem mem_invariantInterior [IsFinite G.t.left] (W : G.U.left.Opens) (x : G.U.left) :
    x ∈ invariantInterior G W ↔
      ¬ ∃ r : G.R.left, G.s.left r ∉ W ∧ G.t.left r = x := Iff.rfl

/-- The invariant interior is contained in the original open. -/
theorem invariantInterior_le [IsFinite G.t.left] (W : G.U.left.Opens) :
    invariantInterior G W ≤ W := by
  intro x hx
  by_contra hxW
  have hs : G.s.left (G.e.left x) = x := by
    simpa using congrArg (fun f ↦ f.left x) G.identity_source
  have ht : G.t.left (G.e.left x) = x := by
    simpa using congrArg (fun f ↦ f.left x) G.identity_target
  exact hx ⟨G.e.left x, by simpa [Set.mem_preimage, hs] using hxW, ht⟩

/-- Any arrow whose source is in the invariant interior has target in `W`. -/
theorem preimage_invariantInterior_le [IsFinite G.t.left] (W : G.U.left.Opens) :
    G.s.left ⁻¹ᵁ invariantInterior G W ≤ G.t.left ⁻¹ᵁ W := by
  intro r hr
  by_contra hrt
  change G.t.left r ∉ W at hrt
  have hs : G.s.left (G.i.left r) = G.t.left r := by
    simpa using congrArg (fun f ↦ f.left r) G.inverse_source
  have ht : G.t.left (G.i.left r) = G.s.left r := by
    simpa using congrArg (fun f ↦ f.left r) G.inverse_target
  exact hr ⟨G.i.left r, by simpa [Set.mem_preimage, hs] using hrt, ht⟩

/-- The saturation complement is invariant under the groupoid relation. -/
theorem invariantInterior_isOpenInvariant [IsFinite G.t.left] (W : G.U.left.Opens) :
    G.toPreRelation.IsOpenInvariant (invariantInterior G W) := sorry

/-- An orbit already contained in `W` lies in the invariant interior of `W`. -/
theorem orbit_subset_invariantInterior [IsFinite G.t.left] (u : G.U.left)
    (W : G.U.left.Opens) (hW : G.t.left '' (G.s.left ⁻¹' {u}) ⊆ W) :
    G.t.left '' (G.s.left ⁻¹' {u}) ⊆ invariantInterior G W := sorry

/-- The principal-open section selected by native finite-prime avoidance. -/
def orbitSection [IsFinite G.s.left] [IsFinite G.t.left] (u : G.U.left)
    (W : G.U.left.affineOpens) (hW : G.t.left '' (G.s.left ⁻¹' {u}) ⊆ W) :
    Γ(G.U.left, W) :=
  (exists_affine_basicOpen_contains_finite W (G.t.left '' (G.s.left ⁻¹' {u}))
    ((G.s.left.finite_preimage_singleton u).image G.t.left)
    (invariantInterior G W) hW (orbit_subset_invariantInterior G u W hW)).choose

/-- The selected principal open contains the orbit and lies in the invariant interior. -/
theorem orbitSection_spec [IsFinite G.s.left] [IsFinite G.t.left] (u : G.U.left)
    (W : G.U.left.affineOpens) (hW : G.t.left '' (G.s.left ⁻¹' {u}) ⊆ W) :
    G.t.left '' (G.s.left ⁻¹' {u}) ⊆ G.U.left.basicOpen (orbitSection G u W hW) ∧
      G.U.left.basicOpen (orbitSection G u W hW) ≤ invariantInterior G W :=
  (exists_affine_basicOpen_contains_finite W (G.t.left '' (G.s.left ⁻¹' {u}))
    ((G.s.left.finite_preimage_singleton u).image G.t.left)
    (invariantInterior G W) hW (orbit_subset_invariantInterior G u W hW)).choose_spec

/-- Pull back a section on `W` along the target map over the source inverse image of the
invariant interior. -/
def targetSection [IsFinite G.t.left] (W : G.U.left.Opens) (f : Γ(G.U.left, W)) :
    Γ(G.R.left, G.s.left ⁻¹ᵁ invariantInterior G W) :=
  G.t.left.appLE W (G.s.left ⁻¹ᵁ invariantInterior G W)
    (preimage_invariantInterior_le G W) f

/-- The norm section of 03JE, using an actual norm supplied for the source morphism. -/
def normSectionOfNorm [IsFinite G.t.left] (N : Scheme.FiniteMorphismNorm G.s.left)
    (W : G.U.left.Opens) (f : Γ(G.U.left, W)) : Γ(G.U.left, invariantInterior G W) :=
  N.app (invariantInterior G W) (targetSection G W f)

/-- The actual nonvanishing open of the norm section. -/
def normCutOfNorm [IsFinite G.t.left] (N : Scheme.FiniteMorphismNorm G.s.left)
    (W : G.U.left.Opens) (f : Γ(G.U.left, W)) : G.U.left.Opens :=
  G.U.left.basicOpen (normSectionOfNorm G N W f)

/-- The norm cut is contained in the invariant interior on which its section is defined. -/
theorem normCutOfNorm_le [IsFinite G.t.left] (N : Scheme.FiniteMorphismNorm G.s.left)
    (W : G.U.left.Opens) (f : Γ(G.U.left, W)) :
    normCutOfNorm G N W f ≤ invariantInterior G W :=
  G.U.left.basicOpen_le _

end AlgebraicGeometry.GroupoidScheme.AffineOpenConstruction
