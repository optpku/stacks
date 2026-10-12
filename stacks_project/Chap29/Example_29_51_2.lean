/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.BinarySequence
import StacksCheckRecall

open AlgebraicGeometry PrimeSpectrum
open AlgebraicGeometry.BinarySequenceSpectrum
open AlgebraicGeometry.BinarySequenceSpectrum.DoubleAlong
open scoped AlgebraicGeometry PrimeSpectrum

/- Example 29.51.2 (1): the ring of binary sequences. -/
@[stacks 03HY] #check (CoordinateRing : Type)

/- Example 29.51.2 (2): the binary-sequence spectrum. -/
@[stacks 03HY] #check (spectrum : Scheme)

/- Example 29.51.2 (3): the coordinate projections. -/
@[stacks 03HY] #check (projection : ℕ → CoordinateRing →+* ZMod 2)

/- Example 29.51.2 (4): binary sequences are idempotent. -/
@[stacks 03HY] #check (BooleanRing.mul_self : ∀ a : CoordinateRing, a * a = a)

/- Example 29.51.2 (5): every prime ideal is maximal. -/
@[stacks 03HY] #check
  (primeIdeal_isMaximal : ∀ p : PrimeSpectrum CoordinateRing, p.asIdeal.IsMaximal)

/- Example 29.51.2 (6): every residue field has cardinality two. -/
@[stacks 03HY] #check
  (residueField_natCard_eq_two : ∀ p : PrimeSpectrum CoordinateRing,
    Nat.card p.asIdeal.ResidueField = 2)

/- Example 29.51.2 (7): the spectrum is compact. -/
@[stacks 03HY] #check (inferInstance : CompactSpace spectrum)

/- Example 29.51.2 (8): the spectrum is totally disconnected. -/
@[stacks 03HY] #check (totallyDisconnected : TotallyDisconnectedSpace spectrum)

/- Example 29.51.2 (9): the coordinate points. -/
@[stacks 03HY] #check (projectionPoint : ℕ → PrimeSpectrum CoordinateRing)

/- Example 29.51.2 (10): coordinate points are open. -/
@[stacks 03HY] #check
  (projectionPoint_isOpen : ∀ n : ℕ,
    IsOpen ({projectionPoint n} : Set (PrimeSpectrum CoordinateRing)))

/- Example 29.51.2 (11): there is a closed point which is not open. -/
@[stacks 03HY] #check
  (exists_closedPoint_not_open : ∃ x : spectrum,
    IsClosed ({x} : Set spectrum) ∧ ¬ IsOpen ({x} : Set spectrum))

/- Example 29.51.2 (12): every point is generic. -/
@[stacks 03HY] #check (mem_genericPoints : ∀ x : spectrum, x ∈ genericPoints spectrum)

/- Example 29.51.2 (13): the punctured open is the complement of the point. -/
@[stacks 03HY] #check
  (coe_puncturedOpen : ∀ (x : spectrum) (hx : IsClosed ({x} : Set spectrum)),
    (puncturedOpen x hx : Set spectrum) = ({x} : Set spectrum)ᶜ)

/- Example 29.51.2 (14): the doubled scheme. -/
@[stacks 03HY] #check
  (scheme : ∀ (x : spectrum) (hx : IsClosed ({x} : Set spectrum)), Scheme)

/- Example 29.51.2 (15): the fold from the doubled scheme. -/
@[stacks 03HY] #check
  (fold : ∀ (x : spectrum) (hx : IsClosed ({x} : Set spectrum)), scheme x hx ⟶ spectrum)

/- Example 29.51.2 (16): the doubled points. -/
@[stacks 03HY] #check
  (point : ∀ (x : spectrum) (hx : IsClosed ({x} : Set spectrum)) (i : Fin 2), scheme x hx)

/- Example 29.51.2 (17): the two doubled copies are distinct at a non-open point. -/
@[stacks 03HY] #check
  (point_zero_ne_one : ∀ (x : spectrum) (hx : IsClosed ({x} : Set spectrum)),
    ¬ IsOpen ({x} : Set spectrum) → point x hx 0 ≠ point x hx 1)

/- Example 29.51.2 (18): folding either copy returns the original point. -/
@[stacks 03HY] #check
  (fold_point : ∀ (x : spectrum) (hx : IsClosed ({x} : Set spectrum)) (i : Fin 2),
    (fold x hx).base (point x hx i) = x)

/- Example 29.51.2 (19): the fold is quasi-compact. -/
@[stacks 03HY] #check
  (fold_quasiCompact : ∀ (x : spectrum) (hx : IsClosed ({x} : Set spectrum)),
    QuasiCompact (fold x hx))

/- Example 29.51.2 (20): the fold is of finite type. -/
@[stacks 03HY] #check
  (fold_finiteType : ∀ (x : spectrum) (hx : IsClosed ({x} : Set spectrum)),
    Scheme.Hom.FiniteType (fold x hx))

/- Example 29.51.2 (21): the fold has finite fibers. -/
@[stacks 03HY] #check
  (fold_finiteFibers : ∀ (x : spectrum) (hx : IsClosed ({x} : Set spectrum)) (s : spectrum),
    ({y : scheme x hx | (fold x hx).base y = s} : Set (scheme x hx)).Finite)

/- Example 29.51.2 (22): the fold is not quasi-separated at a non-open point. -/
@[stacks 03HY] #check
  (fold_not_quasiSeparated : ∀ (x : spectrum) (hx : IsClosed ({x} : Set spectrum)),
    ¬ IsOpen ({x} : Set spectrum) → ¬ QuasiSeparated (fold x hx))

/- Example 29.51.2 (23): inverse images of neighborhoods of the point are nonaffine. -/
@[stacks 03HY] #check
  (preimage_not_isAffine : ∀ (x : spectrum) (hx : IsClosed ({x} : Set spectrum)),
    ¬ IsOpen ({x} : Set spectrum) → ∀ (V : spectrum.Opens), x ∈ V →
      ¬ IsAffine ((fold x hx) ⁻¹ᵁ V).toScheme)

/- Example 29.51.2 (24): no affine fiber neighborhood has finite restriction. -/
@[stacks 03HY] #check
  (no_finiteRestriction_on_affineFiberNeighborhood : ∀ (x : spectrum)
    (hx : IsClosed ({x} : Set spectrum)), ¬ IsOpen ({x} : Set spectrum) →
    ¬ ∃ (U : (scheme x hx).Opens) (V : spectrum.Opens)
      (_ : IsAffineOpen U) (_ : IsAffineOpen V) (_ : x ∈ V)
      (hUV : U ≤ fold x hx ⁻¹ᵁ V)
      (_ : ∀ y : scheme x hx, (fold x hx).base y = x → y ∈ U),
      IsFinite ((fold x hx).resLE V U hUV))

/- Example 29.51.2 (25): no affine target neighborhood has finite restriction. -/
@[stacks 03HY] #check
  (no_finiteRestriction_over_affineNeighborhood : ∀ (x : spectrum)
    (hx : IsClosed ({x} : Set spectrum)), ¬ IsOpen ({x} : Set spectrum) →
    ¬ ∃ (V : spectrum.Opens) (_ : IsAffineOpen V) (_ : x ∈ V),
      IsFinite (fold x hx ∣_ V))
