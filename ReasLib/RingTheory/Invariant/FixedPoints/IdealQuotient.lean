/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Invariant.FixedPoints.Charpoly
public import ReasLib.RingTheory.Invariant.Quotient
public import ReasLib.RingTheory.RingHom.ShiftPower

@[expose] public section

open scoped Pointwise

/-!
# Quotients of fixed-point subrings

This leaf owns the algebraic construction attached to an ideal of a fixed-point subring. The
quotient action itself is delegated to `Ideal.Quotient.action`; this module only supplies the
canonical extension ideal and the induced fixed-points map. Spectrum and residue-field
consequences live in the companion `Spectrum` leaf.
@stack 0H35
-/

universe u v

namespace FixedPoints.Quotient

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [MulSemiringAction G R]

/-- The extension of an ideal of `FixedPoints.subring R G` to the ambient ring `R`. -/
@[stacks 0H35 "fixed-subring ideal extension"]
abbrev ideal (J : Ideal (FixedPoints.subring R G)) : Ideal R :=
  Ideal.map (FixedPoints.subring R G).subtype J

/-- The extension ideal is stable under the whole group action. -/
@[stacks 0H35 "stability of a fixed-subring ideal extension"]
theorem ideal_isStable (J : Ideal (FixedPoints.subring R G)) :
    (ideal J).IsStable G := sorry
-- Proof strategy: for each `g`, rewrite pointwise scalar action by
-- `Ideal.pointwise_smul_def` and combine the two ideal maps with `Ideal.map_map`; the composite
-- ring hom equals the fixed-subring subtype because every source element is fixed by `g`.

/-- The pointwise form of stability for an extended fixed-subring ideal. -/
@[simp, stacks 0H35 "pointwise stability of a fixed-subring ideal extension"]
theorem ideal_smul (J : Ideal (FixedPoints.subring R G)) (g : G) :
    g • ideal J = ideal J := sorry
-- Proof strategy: this is the value of `ideal_isStable J` at `g` after unfolding
-- `Ideal.IsStable`.

/-- The canonical action on the quotient by an extended fixed-subring ideal.

The stability proof is a named mathematical input rather than a global instance, since quotient
actions depend on the chosen ideal. -/
@[reducible, stacks 0H35 "quotient action of a fixed-subring ideal extension"]
def action (J : Ideal (FixedPoints.subring R G)) :
    MulSemiringAction G (R ⧸ ideal J) :=
  Ideal.Quotient.action (ideal J) (ideal_isStable J)

/-- The fixed-point subring of the quotient by the extended ideal. -/
@[stacks 0H35 "fixed points of the extended ideal quotient"]
abbrev fixed (J : Ideal (FixedPoints.subring R G)) :=
  -- Local instance justification (defeq pin): the fixed subring must use the named quotient action.
  letI := action J
  FixedPoints.subring (R ⧸ ideal J) G

/-- The quotient projection as an equivariant ring homomorphism. -/
@[stacks 0H35 "equivariant quotient projection for a fixed-subring ideal"]
def mkHom (J : Ideal (FixedPoints.subring R G)) :
    -- Local instance justification (defeq pin): the codomain action is the canonical action above.
    letI := action J
    R →+*[G] R ⧸ ideal J :=
  -- Local instance justification (defeq pin): the equivariance field must see the same action.
  letI := action J
  Ideal.Quotient.mkHom (ideal J) (ideal_isStable J)

/-- Factor the generic fixed-points quotient map through any smaller ideal of the fixed subring.

The specialization `map J` below uses `I = ideal J` and `hJ = Ideal.le_comap_map`; exposing this
bridge keeps later quotient constructions from repeating the raw `Ideal.quotientMap` expression. -/
@[stacks 0H35 "fixed-points quotient map factorization"]
def mapOfLE (I : Ideal R) (hI : I.IsStable G)
    (J : Ideal (FixedPoints.subring R G))
    (hJ : J ≤ Ideal.comap (FixedPoints.subring R G).subtype I) :
    -- Local instance justification (defeq pin): the target fixed subring uses the action selected
    -- by `hI`.
    letI := Ideal.Quotient.action I hI
    FixedPoints.subring R G ⧸ J →+* FixedPoints.subring (R ⧸ I) G :=
  -- Local instance justification (defeq pin): the generic fixed-points map and quotient factor
  -- must share the same proof-dependent action.
  letI := Ideal.Quotient.action I hI
  (Ideal.Quotient.fixedPointsMap I hI).comp
    (Ideal.quotientMap _ (RingHom.id _) hJ)

/-- The general fixed-points quotient factorization on a representative. -/
@[simp, stacks 0H35 "fixed-points quotient factorization on representatives"]
theorem mapOfLE_mk (I : Ideal R) (hI : I.IsStable G)
    (J : Ideal (FixedPoints.subring R G))
    (hJ : J ≤ Ideal.comap (FixedPoints.subring R G).subtype I)
    (x : FixedPoints.subring R G) :
    -- Local instance justification (defeq pin): this computation uses the quotient action
    -- selected by `hI` in the codomain fixed subring.
    letI := Ideal.Quotient.action I hI
    ((mapOfLE I hI J hJ (Ideal.Quotient.mk J x) :
        FixedPoints.subring (R ⧸ I) G) : R ⧸ I) = Ideal.Quotient.mk I x := sorry
-- Proof strategy: unfold `mapOfLE`, rewrite `Ideal.quotientMap` on the representative, then use
-- `Ideal.Quotient.fixedPointsMap_mk`; all quotient actions are pinned to the same proof `hI`.

/-- Composing the general factorization with the source quotient projection recovers the
equivariant quotient projection restricted to fixed points. -/
@[stacks 0H35 "fixed-points quotient factorization composition"]
theorem mapOfLE_comp_mk (I : Ideal R) (hI : I.IsStable G)
    (J : Ideal (FixedPoints.subring R G))
    (hJ : J ≤ Ideal.comap (FixedPoints.subring R G).subtype I) :
    -- Local instance justification (defeq pin): both maps use the quotient action selected by
    -- `hI`.
    letI := Ideal.Quotient.action I hI
    (mapOfLE I hI J hJ).comp (Ideal.Quotient.mk J) =
      (Ideal.Quotient.mkHom I hI).fixedPoints := sorry
-- Proof strategy: apply `Ideal.Quotient.ringHom_ext` to the source quotient and evaluate on a
-- fixed element; after coercing the target subtype, `mapOfLE_mk` identifies both sides with
-- `Ideal.Quotient.mk I x`.

/-- The canonical map from `FixedPoints.subring R G ⧸ J` to the fixed subring of
`R ⧸ FixedPoints.Quotient.ideal J`. -/
@[stacks 0H35 "fixed-subring quotient map"]
def map (J : Ideal (FixedPoints.subring R G)) :
    -- Local instance justification (defeq pin): retain the proof-dependent quotient action in the
    -- codomain type of the public map.
    letI := action J
    FixedPoints.subring R G ⧸ J →+* fixed J :=
  -- Local instance justification (defeq pin): both factors of the composite use this action.
  letI := action J
  mapOfLE (ideal J) (ideal_isStable J) J Ideal.le_comap_map

/-- The fixed-subring quotient map on a representative. -/
@[simp, stacks 0H35 "fixed-subring quotient map on representatives"]
theorem map_mk (J : Ideal (FixedPoints.subring R G))
    (x : FixedPoints.subring R G) :
    -- Local instance justification (defeq pin): this equation is evaluated in the named quotient
    -- action and its fixed-point codomain.
    letI := action J
    ((map J (Ideal.Quotient.mk J x) : fixed J) : R ⧸ ideal J) =
      Ideal.Quotient.mk (ideal J) x := sorry
-- Proof strategy: unfold `map` and specialize `mapOfLE_mk` to `I = ideal J`,
-- `hI = ideal_isStable J`, and `hJ = Ideal.le_comap_map`.

/-- The fixed-subring quotient map composed with the source quotient projection is the restricted
equivariant quotient projection. -/
@[stacks 0H35 "fixed-subring quotient map composition"]
theorem map_comp_mk (J : Ideal (FixedPoints.subring R G)) :
    -- Local instance justification (defeq pin): the two maps share the same quotient action.
    letI := action J
    (map J).comp (Ideal.Quotient.mk J) = (mkHom J).fixedPoints := sorry
-- Proof strategy: unfold `map` and `mkHom`, then specialize `mapOfLE_comp_mk` with the canonical
-- extension ideal and `Ideal.le_comap_map`; retain the named quotient action throughout.

/-- Every fixed class in `fixed J` has a monic polynomial over
`FixedPoints.subring R G ⧸ J` whose image is its shifted
power. -/
@[stacks 0H35 "monic polynomial over a fixed-subring quotient"]
theorem exists_monic (J : Ideal (FixedPoints.subring R G)) [Finite G]
    (b : fixed J) :
    ∃ P : Polynomial (FixedPoints.subring R G ⧸ J),
      P.Monic ∧ P.map (map J) = (Polynomial.X - Polynomial.C b) ^ Nat.card G := sorry
-- Proof strategy: apply `MulSemiringActionHom.exists_monic_map_eq_orbit` to the equivariant
-- quotient map `mkHom J` and `Ideal.Quotient.mk_surjective`.  Map the resulting polynomial over
-- `FixedPoints.subring R G` through `Ideal.Quotient.mk J`; monicity is preserved, and
-- `Polynomial.map_map` together with `map_comp_mk` gives the required target identity.

/-- A kernel element of the fixed-subring quotient map satisfies the orbit-power identity. -/
@[stacks 0H35 "kernel orbit-power identity"]
theorem kernel_pow (J : Ideal (FixedPoints.subring R G)) [Finite G]
    (a : RingHom.ker (map J)) :
    (Polynomial.X - Polynomial.C a.1) ^ Nat.card G = Polynomial.X ^ Nat.card G := sorry
-- Proof strategy: choose a representative `x : FixedPoints.subring R G` of `a.1`.  The kernel
-- equation and `map_mk` imply `(x : R) ∈ ideal J`.  Install `Fintype.ofFinite G` and compare
-- coefficients: after mapping `(X - C x) ^ Fintype.card G` through the fixed-subring subtype,
-- `MulSemiringAction.charpoly_eq` identifies it with the orbit polynomial of `x`; every
-- coefficient below the leading one lies in `J` by `FixedPoints.charpolyCoeff_mem`, the leading
-- coefficients agree by `MulSemiringAction.monic_charpoly`, and higher coefficients vanish.
-- Apply `Polynomial.ext`, quotient coefficients by `Ideal.Quotient.mk J`, and finally rewrite
-- `Nat.card_eq_fintype_card` and the chosen representative equality.

/-- The fixed-subring quotient map is shift-power generated. -/
@[stacks 0H35 "shift-power generation of the fixed-subring quotient map"]
theorem isGenerated (J : Ideal (FixedPoints.subring R G)) [Finite G] :
    RingHom.ShiftPower.IsGenerated (map J) := sorry
-- Proof strategy: give `map J` its canonical algebra structure, prove its adjoin is top
-- elementwise, and use `exists_monic J b` as the shift-power witness for each `b : fixed J`;
-- finish with `Algebra.subset_adjoin`.

/-- The fixed-subring quotient map is integral. -/
@[stacks 0H35 "integrality of the fixed-subring quotient map"]
theorem isIntegral (J : Ideal (FixedPoints.subring R G)) [Finite G] :
    (map J).IsIntegral := sorry
-- Proof strategy: apply `RingHom.ShiftPower.isIntegral` to `isGenerated J`.

end FixedPoints.Quotient
