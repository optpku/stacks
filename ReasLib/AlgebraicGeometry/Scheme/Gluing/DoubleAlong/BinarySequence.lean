/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.QuasiSeparated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.GenericFiber

/-!
# The spectrum of a countable product of binary fields

This file constructs the spectrum of the countable product of copies of `ZMod 2` and the
scheme obtained by doubling a nonisolated point along its open complement.
-/

@[expose] public section

open CategoryTheory PrimeSpectrum
open scoped AlgebraicGeometry PrimeSpectrum

noncomputable section

namespace AlgebraicGeometry.BinarySequenceSpectrum

/-- The ring of binary sequences with pointwise operations. -/
@[stacks 03HY]
abbrev CoordinateRing :=
  ℕ → ZMod 2

/-- Binary sequences form a Boolean ring under pointwise operations. -/
instance instBooleanRingCoordinateRing : BooleanRing CoordinateRing :=
  { (inferInstance : Ring CoordinateRing) with
    isIdempotentElem := fun a ↦ by
      funext n
      let z := a n
      change z * z = z
      have hz : z.val = 0 ∨ z.val = 1 :=
        Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp (ZMod.val_lt z))
      rw [← ZMod.natCast_zmod_val z]
      rcases hz with hz | hz <;> simp [hz] }

/-- The affine spectrum of the ring of binary sequences. -/
@[stacks 03HY]
abbrev spectrum : Scheme :=
  Spec (CommRingCat.of CoordinateRing)

/-- Evaluation of a binary sequence at one coordinate. -/
@[stacks 03HY]
abbrev projection (n : ℕ) : CoordinateRing →+* ZMod 2 :=
  Pi.evalRingHom (fun _ : ℕ ↦ ZMod 2) n

/-- The point of the binary-sequence spectrum induced by evaluation at one coordinate. -/
@[stacks 03HY]
def projectionPoint (n : ℕ) : PrimeSpectrum CoordinateRing :=
  PrimeSpectrum.comap (projection n) (IsLocalRing.closedPoint (ZMod 2))

/-- Every prime ideal of the ring of binary sequences is maximal. -/
@[stacks 03HY]
theorem primeIdeal_isMaximal (p : PrimeSpectrum CoordinateRing) :
    p.asIdeal.IsMaximal := sorry

/-- The residue field at every point of the binary-sequence spectrum has two elements. -/
@[stacks 03HY]
theorem residueField_natCard_eq_two (p : PrimeSpectrum CoordinateRing) :
    Nat.card p.asIdeal.ResidueField = 2 := sorry

/-- The binary-sequence spectrum is totally disconnected. -/
@[stacks 03HY]
theorem totallyDisconnected : TotallyDisconnectedSpace spectrum := sorry

/-- Total disconnectedness of the binary-sequence spectrum is available canonically. -/
instance instTotallyDisconnectedSpaceSpectrum : TotallyDisconnectedSpace spectrum :=
  totallyDisconnected

/-- Every coordinate-evaluation point is open in the binary-sequence spectrum. -/
@[stacks 03HY]
theorem projectionPoint_isOpen (n : ℕ) :
    IsOpen ({projectionPoint n} : Set (PrimeSpectrum CoordinateRing)) := sorry

/-- The binary-sequence spectrum has a closed point which is not open. -/
@[stacks 03HY]
theorem exists_closedPoint_not_open :
    ∃ x : spectrum, IsClosed ({x} : Set spectrum) ∧ ¬ IsOpen ({x} : Set spectrum) := sorry

/-- Every point of the totally disconnected binary-sequence spectrum is a generic point of an
irreducible component. -/
@[stacks 03HY]
theorem mem_genericPoints (x : spectrum) :
    x ∈ genericPoints spectrum := sorry

namespace DoubleAlong

/-- The open complement of a closed point in the binary-sequence spectrum. -/
@[stacks 03HY]
def puncturedOpen (x : spectrum) (hx : IsClosed ({x} : Set spectrum)) : spectrum.Opens :=
  ⟨({x} : Set spectrum)ᶜ, hx.isOpen_compl⟩

/-- The underlying set of `puncturedOpen x hx` is the complement of `{x}`. -/
@[stacks 03HY, simp]
theorem coe_puncturedOpen (x : spectrum) (hx : IsClosed ({x} : Set spectrum)) :
    (puncturedOpen x hx : Set spectrum) = ({x} : Set spectrum)ᶜ := sorry

/-- The scheme obtained by gluing two copies of the binary-sequence spectrum along the
complement of a closed point. -/
@[stacks 03HY]
noncomputable def scheme (x : spectrum) (hx : IsClosed ({x} : Set spectrum)) : Scheme :=
  Scheme.doubleAlong (puncturedOpen x hx)

/-- The fold from the doubled binary-sequence spectrum to the original spectrum. -/
@[stacks 03HY]
noncomputable def fold (x : spectrum) (hx : IsClosed ({x} : Set spectrum)) :
    scheme x hx ⟶ spectrum :=
  Scheme.DoubleAlong.fold (puncturedOpen x hx)

/-- The copy of a point in one of the two canonical charts of the doubled spectrum. -/
@[stacks 03HY]
noncomputable def point (x : spectrum) (hx : IsClosed ({x} : Set spectrum))
    (i : Fin 2) : scheme x hx :=
  Scheme.DoubleAlong.point (puncturedOpen x hx) i x

/-- The two copies of a closed point are distinct when that point is not open. -/
@[stacks 03HY]
theorem point_zero_ne_one (x : spectrum) (hx : IsClosed ({x} : Set spectrum))
    (hxo : ¬ IsOpen ({x} : Set spectrum)) :
    point x hx 0 ≠ point x hx 1 := sorry

/-- Folding either canonical copy of a point returns that point. -/
@[stacks 03HY, simp]
theorem fold_point (x : spectrum) (hx : IsClosed ({x} : Set spectrum)) (i : Fin 2) :
    (fold x hx).base (point x hx i) = x := sorry

/-- The fold of the doubled binary-sequence spectrum is quasi-compact. -/
@[stacks 03HY]
theorem fold_quasiCompact (x : spectrum) (hx : IsClosed ({x} : Set spectrum)) :
    QuasiCompact (fold x hx) := sorry

/-- The fold of the doubled binary-sequence spectrum is of finite type. -/
@[stacks 03HY]
theorem fold_finiteType (x : spectrum) (hx : IsClosed ({x} : Set spectrum)) :
    Scheme.Hom.FiniteType (fold x hx) := sorry

/-- Every point-set fiber of the fold of the doubled spectrum is finite. -/
@[stacks 03HY]
theorem fold_finiteFibers (x : spectrum) (hx : IsClosed ({x} : Set spectrum)) :
    ∀ s : spectrum, ({y : scheme x hx | (fold x hx).base y = s} : Set (scheme x hx)).Finite :=
  sorry

/-- Doubling a non-open closed point produces a fold which is not quasi-separated. -/
@[stacks 03HY]
theorem fold_not_quasiSeparated (x : spectrum) (hx : IsClosed ({x} : Set spectrum))
    (hxo : ¬ IsOpen ({x} : Set spectrum)) :
    ¬ QuasiSeparated (fold x hx) := sorry

/-- The inverse image of every open neighborhood of the doubled point is nonaffine. -/
@[stacks 03HY]
theorem preimage_not_isAffine (x : spectrum) (hx : IsClosed ({x} : Set spectrum))
    (hxo : ¬ IsOpen ({x} : Set spectrum)) (V : spectrum.Opens) (hxV : x ∈ V) :
    ¬ IsAffine ((fold x hx) ⁻¹ᵁ V).toScheme := sorry

/-- No affine source neighborhood of the doubled fiber has finite restriction over an affine
neighborhood of the original point. -/
@[stacks 03HY]
theorem no_finiteRestriction_on_affineFiberNeighborhood
    (x : spectrum) (hx : IsClosed ({x} : Set spectrum))
    (hxo : ¬ IsOpen ({x} : Set spectrum)) :
    ¬ ∃ (U : (scheme x hx).Opens) (V : spectrum.Opens)
        (_ : IsAffineOpen U) (_ : IsAffineOpen V) (_ : x ∈ V)
        (hUV : U ≤ fold x hx ⁻¹ᵁ V)
        (_ : ∀ y : scheme x hx, (fold x hx).base y = x → y ∈ U),
      IsFinite ((fold x hx).resLE V U hUV) := sorry

/-- The fold is not finite over the inverse image of any affine neighborhood of the doubled
point. -/
@[stacks 03HY]
theorem no_finiteRestriction_over_affineNeighborhood
    (x : spectrum) (hx : IsClosed ({x} : Set spectrum))
    (hxo : ¬ IsOpen ({x} : Set spectrum)) :
    ¬ ∃ (V : spectrum.Opens) (_ : IsAffineOpen V) (_ : x ∈ V),
      IsFinite (fold x hx ∣_ V) := sorry

end DoubleAlong

end AlgebraicGeometry.BinarySequenceSpectrum
