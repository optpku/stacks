/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PrimeSpectrum.Specialization
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.6.24: a point `p` generalizes `q` in `PrimeSpectrum R` exactly when
`p.asIdeal ≤ q.asIdeal`. The companion checks characterize closed points by maximal
ideals and the absence of proper specializations, and generic points of irreducible
components by minimal prime ideals and the absence of proper generalizations. -/
@[stacks 02DE] #check (PrimeSpectrum.generalization_iff_subset :
  ∀ (R : Type u) [CommSemiring R] (p q : PrimeSpectrum R), p ⤳ q ↔ p.asIdeal ≤ q.asIdeal)

variable (R : Type u) [CommSemiring R]

/- Companion: `x ≤ y` iff `y ∈ closure {x}`. -/
#check (PrimeSpectrum.le_iff_mem_closure :
  ∀ x y : PrimeSpectrum R, x ≤ y ↔ y ∈ closure ({x} : Set (PrimeSpectrum R)))

/- Companion: `x.asIdeal ≤ y.asIdeal` iff `x ≤ y`. -/
#check (PrimeSpectrum.asIdeal_le_asIdeal :
  ∀ x y : PrimeSpectrum R, x.asIdeal ≤ y.asIdeal ↔ x ≤ y)

/- Companion: `x ⤳ y` iff `y ∈ closure {x}`. -/
#check (specializes_iff_mem_closure :
  ∀ {x y : PrimeSpectrum R}, x ⤳ y ↔ y ∈ closure ({x} : Set (PrimeSpectrum R)))

/- Companion: closed points correspond to maximal ideals. -/
#check (PrimeSpectrum.mem_closedPoints_iff_isMaximal R :
  ∀ p : PrimeSpectrum R, p ∈ closedPoints (PrimeSpectrum R) ↔ p.asIdeal.IsMaximal)

/- Companion: closed points have no proper specialization. -/
#check (PrimeSpectrum.mem_closedPoints_iff_no_proper_specialization R :
  ∀ p : PrimeSpectrum R,
    p ∈ closedPoints (PrimeSpectrum R) ↔ ∀ q : PrimeSpectrum R, p ⤳ q → q = p)

/- Companion: singleton specialization stability corresponds to maximality. -/
#check (PrimeSpectrum.stableUnderSpecialization_singleton :
  ∀ {x : PrimeSpectrum R}, StableUnderSpecialization {x} ↔ x.asIdeal.IsMaximal)

/- Companion: `IsMax x` iff `x.asIdeal.IsMaximal` on the inclusion/specialization order. -/
#check (PrimeSpectrum.isMax_iff :
  ∀ {x : PrimeSpectrum R}, IsMax x ↔ x.asIdeal.IsMaximal)

/- Companion: `IsClosed {x}` iff `x.asIdeal.IsMaximal`. -/
#check (PrimeSpectrum.isClosed_singleton_iff_isMaximal :
  ∀ x : PrimeSpectrum R, IsClosed ({x} : Set (PrimeSpectrum R)) ↔ x.asIdeal.IsMaximal)

/- Companion: `x ∈ closedPoints X` iff `IsClosed {x}`. -/
#check (mem_closedPoints_iff :
  ∀ {x : PrimeSpectrum R}, x ∈ closedPoints (PrimeSpectrum R) ↔ IsClosed {x})

/- Companion: a closed set is stable under specialization. -/
#check (IsClosed.stableUnderSpecialization :
  ∀ {s : Set (PrimeSpectrum R)}, IsClosed s → StableUnderSpecialization s)

/- Companion: `closure s = s` iff `IsClosed s`. -/
#check (closure_eq_iff_isClosed :
  ∀ {s : Set (PrimeSpectrum R)}, closure s = s ↔ IsClosed s)

/- Companion: generic points are generic for irreducible components, even in a
reducible space. -/
#check (genericPoints : ∀ (X : Type u) [TopologicalSpace X], Set X)

/- Companion: generic points of the prime spectrum correspond to minimal primes. -/
#check (PrimeSpectrum.mem_genericPoints_iff_mem_minimalPrimes R :
  ∀ p : PrimeSpectrum R, p ∈ genericPoints (PrimeSpectrum R) ↔ p.asIdeal ∈ minimalPrimes R)

/- Companion: generic points have no proper generalization. -/
#check (PrimeSpectrum.mem_genericPoints_iff_no_proper_generalization R :
  ∀ p : PrimeSpectrum R,
    p ∈ genericPoints (PrimeSpectrum R) ↔ ∀ q : PrimeSpectrum R, q ⤳ p → q = p)

/- Companion: `IsGenericPoint x S` iff `∀ y, x ⤳ y ↔ y ∈ S`. -/
#check (isGenericPoint_iff_specializes :
  ∀ {x : PrimeSpectrum R} {S : Set (PrimeSpectrum R)},
    IsGenericPoint x S ↔ ∀ y, x ⤳ y ↔ y ∈ S)

/- Companion: a point of `genericPoints α` is a generic point of its irreducible component. -/
#check (genericPoints.isGenericPoint :
  ∀ x : genericPoints (PrimeSpectrum R), IsGenericPoint x.val (genericPoints.component x).val)

/- Companion: singleton generalization stability corresponds to minimal primes. -/
#check (PrimeSpectrum.stableUnderGeneralization_singleton :
  ∀ {x : PrimeSpectrum R}, StableUnderGeneralization {x} ↔ x.asIdeal ∈ minimalPrimes R)

/- Companion: `IsMin x` iff `x.asIdeal ∈ minimalPrimes R`. -/
#check (PrimeSpectrum.isMin_iff :
  ∀ {x : PrimeSpectrum R}, IsMin x ↔ x.asIdeal ∈ minimalPrimes R)
