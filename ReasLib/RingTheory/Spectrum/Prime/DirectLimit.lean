module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Inverse limits of prime spectra along directed ring systems

Compatible families of primes along a directed system of commutative rings
form the inverse limit of the sets `PrimeSpectrum (A i)`. This type is in
bijection with `PrimeSpectrum` of the directed colimit `Ring.DirectLimit`.
-/

@[expose] public section

universe u v

noncomputable section

namespace PrimeSpectrum

section InverseLimit

variable {ι : Type u} [Preorder ι]
variable (A : ι → Type v) [∀ i, CommRing (A i)]
variable (φ : ∀ i j, i ≤ j → A i →+* A j)

/-- A family of primes is compatible when each transition map pulls the later
prime back to the earlier one. -/
def IsCompatible (p : ∀ i, PrimeSpectrum (A i)) : Prop :=
  ∀ ⦃i j⦄ (hij : i ≤ j), comap (φ i j hij) (p j) = p i

/-- The inverse limit of the sets `PrimeSpectrum (A i)`, realized as compatible
families in the product. -/
def inverseLimit :=
  {p : ∀ i, PrimeSpectrum (A i) // IsCompatible A φ p}

/-- The component of a compatible family at the index `i`. -/
def proj (q : inverseLimit A φ) (i : ι) : PrimeSpectrum (A i) :=
  q.val i

/-- The component projection returns the underlying family at `i`. -/
theorem proj_apply (q : inverseLimit A φ) (i : ι) :
    proj A φ q i = q.val i := sorry

/-- Compatibility is equivalent to arising as the components of a point of the
inverse limit. -/
theorem mem_inverseLimit {p : ∀ i, PrimeSpectrum (A i)} :
    IsCompatible A φ p ↔ ∃ q : inverseLimit A φ, ∀ i, proj A φ q i = p i :=
  sorry

/-- Two points of the inverse limit agree when all components agree. -/
theorem inverseLimit_ext {q q' : inverseLimit A φ}
    (h : ∀ i, proj A φ q i = proj A φ q' i) : q = q' := sorry

/-- The underlying family of a point of the inverse limit is compatible. -/
theorem isCompatible_proj (q : inverseLimit A φ) :
    IsCompatible A φ (fun i ↦ proj A φ q i) := sorry

end InverseLimit

section DirectLimit

variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
variable (A : ι → Type v) [∀ i, CommRing (A i)]
variable (φ : ∀ i j, i ≤ j → A i →+* A j)
variable [DirectedSystem A (φ · · ·)]

/-- Pulling a colimit prime back along the stage maps yields a compatible family. -/
theorem isCompatible_comap (p : PrimeSpectrum (Ring.DirectLimit A (φ · · ·))) :
    IsCompatible A φ (fun i ↦ comap (Ring.DirectLimit.of A (φ · · ·) i) p) :=
  sorry

/-- The compatible family of pullbacks of a prime of the directed colimit. -/
def toInverseLimit (p : PrimeSpectrum (Ring.DirectLimit A (φ · · ·))) :
    inverseLimit A φ :=
  ⟨fun i ↦ comap (Ring.DirectLimit.of A (φ · · ·) i) p, isCompatible_comap A φ p⟩

/-- The `i`-component of the forward map is `comap` along the stage map from
`A i`. -/
theorem toInverseLimit_apply (p : PrimeSpectrum (Ring.DirectLimit A (φ · · ·)))
    (i : ι) :
    proj A φ (toInverseLimit A φ p) i =
      comap (Ring.DirectLimit.of A (φ · · ·) i) p := sorry

/-- The colimit prime whose underlying ideal is the directed union of the images
of a compatible family. -/
def ofInverseLimit (q : inverseLimit A φ) :
    PrimeSpectrum (Ring.DirectLimit A (φ · · ·)) where
  asIdeal := ⨆ i, Ideal.map (Ring.DirectLimit.of A (φ · · ·) i) (proj A φ q i).asIdeal
  isPrime := sorry

/-- The inverse map has underlying ideal the directed union of the images of the
components. -/
theorem ofInverseLimit_asIdeal (q : inverseLimit A φ) :
    (ofInverseLimit A φ q).asIdeal =
      ⨆ i, Ideal.map (Ring.DirectLimit.of A (φ · · ·) i) (proj A φ q i).asIdeal :=
  sorry

/-- The set bijection `Spec(colim A i) ≃ lim Spec(A i)` of compatible prime families. -/
def directLimitEquiv :
    PrimeSpectrum (Ring.DirectLimit A (φ · · ·)) ≃ inverseLimit A φ where
  toFun := toInverseLimit A φ
  invFun := ofInverseLimit A φ
  left_inv := sorry
  right_inv := sorry

/-- The equivalence sends a colimit prime to the family of its pullbacks along
the stage maps. -/
theorem directLimitEquiv_apply (p : PrimeSpectrum (Ring.DirectLimit A (φ · · ·)))
    (i : ι) :
    proj A φ (directLimitEquiv A φ p) i =
      comap (Ring.DirectLimit.of A (φ · · ·) i) p := sorry

/-- The inverse equivalence reconstructs the directed-union prime. -/
theorem directLimitEquiv_symm_apply (q : inverseLimit A φ) :
    (directLimitEquiv A φ).symm q = ofInverseLimit A φ q := sorry

/-- The inverse equivalence has the same underlying ideal as `ofInverseLimit`. -/
theorem directLimitEquiv_symm_asIdeal (q : inverseLimit A φ) :
    ((directLimitEquiv A φ).symm q).asIdeal =
      ⨆ i, Ideal.map (Ring.DirectLimit.of A (φ · · ·) i) (proj A φ q i).asIdeal :=
  sorry

end DirectLimit

end PrimeSpectrum
