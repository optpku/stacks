/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
    (ideal J).IsStable G := by
  intro g
  rw [Ideal.pointwise_smul_def, ideal, Ideal.map_map]
  congr 1
  exact RingHom.ext fun x ↦ x.2 g

/-- The pointwise form of stability for an extended fixed-subring ideal. -/
@[simp, stacks 0H35 "pointwise stability of a fixed-subring ideal extension"]
theorem ideal_smul (J : Ideal (FixedPoints.subring R G)) (g : G) :
    g • ideal J = ideal J :=
  ideal_isStable J g

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
        FixedPoints.subring (R ⧸ I) G) : R ⧸ I) = Ideal.Quotient.mk I x := by
  rfl

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
      (Ideal.Quotient.mkHom I hI).fixedPoints := by
  rfl

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
      Ideal.Quotient.mk (ideal J) x := by
  rfl

/-- The fixed-subring quotient map composed with the source quotient projection is the restricted
equivariant quotient projection. -/
@[stacks 0H35 "fixed-subring quotient map composition"]
theorem map_comp_mk (J : Ideal (FixedPoints.subring R G)) :
    -- Local instance justification (defeq pin): the two maps share the same quotient action.
    letI := action J
    (map J).comp (Ideal.Quotient.mk J) = (mkHom J).fixedPoints := by
  rfl

/-- Every fixed class in `fixed J` has a monic polynomial over
`FixedPoints.subring R G ⧸ J` whose image is its shifted
power. -/
@[stacks 0H35 "monic polynomial over a fixed-subring quotient"]
theorem exists_monic (J : Ideal (FixedPoints.subring R G)) [Finite G]
    (b : fixed J) :
    ∃ P : Polynomial (FixedPoints.subring R G ⧸ J),
      P.Monic ∧ P.map (map J) = (Polynomial.X - Polynomial.C b) ^ Nat.card G := by
  classical
  letI := Fintype.ofFinite G
  letI := action J
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (b : R ⧸ ideal J)
  obtain ⟨P, hP, _, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Algebra.IsInvariant.charpoly_mem_lifts (FixedPoints.subring R G) R G r)
    (MulSemiringAction.monic_charpoly G r)
  have hgr (g : G) : Ideal.Quotient.mk (ideal J) (g • r) = (b : R ⧸ ideal J) := by
    calc
      Ideal.Quotient.mk (ideal J) (g • r) = g • Ideal.Quotient.mk (ideal J) r := rfl
      _ = g • (b : R ⧸ ideal J) := congrArg (g • ·) hr
      _ = b := b.2 g
  refine ⟨P.map (Ideal.Quotient.mk J), hPm.map _, ?_⟩
  apply Polynomial.map_injective (fixed J).subtype Subtype.val_injective
  calc
    ((P.map (Ideal.Quotient.mk J)).map (map J)).map (fixed J).subtype =
        (P.map (FixedPoints.subring R G).subtype).map (Ideal.Quotient.mk (ideal J)) := by
      rw [Polynomial.map_map, Polynomial.map_map, Polynomial.map_map]
      rfl
    _ = (MulSemiringAction.charpoly G r).map (Ideal.Quotient.mk (ideal J)) :=
      congrArg (Polynomial.map (Ideal.Quotient.mk (ideal J))) hP
    _ = (Polynomial.X - Polynomial.C (b : R ⧸ ideal J)) ^ Nat.card G := by
      simp [MulSemiringAction.charpoly_eq, Polynomial.map_prod, hgr,
        Nat.card_eq_fintype_card]
    _ = ((Polynomial.X - Polynomial.C b) ^ Nat.card G).map (fixed J).subtype := by
      simp
  rfl

/-- A kernel element of the fixed-subring quotient map satisfies the orbit-power identity. -/
@[stacks 0H35 "kernel orbit-power identity"]
theorem kernel_pow (J : Ideal (FixedPoints.subring R G)) [Finite G]
    (a : RingHom.ker (map J)) :
    (Polynomial.X - Polynomial.C a.1) ^ Nat.card G = Polynomial.X ^ Nat.card G := by
  classical
  letI := Fintype.ofFinite G
  rcases subsingleton_or_nontrivial (FixedPoints.subring R G) with h | h
  · exact Subsingleton.elim _ _
  · obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective a.1
    have hxI : (x : R) ∈ ideal J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have ha := congrArg Subtype.val (show map J a.1 = 0 from a.2)
      rwa [← hx, map_mk] at ha
    let p : Polynomial (FixedPoints.subring R G) :=
      (Polynomial.X - Polynomial.C x) ^ Fintype.card G
    have hp : p.map (FixedPoints.subring R G).subtype =
        MulSemiringAction.charpoly G (x : R) := by
      have hfixed (g : G) : g • (x : R) = (x : R) := x.2 g
      simp [p, MulSemiringAction.charpoly_eq, hfixed]
    have hcoeff (n : ℕ) : p.coeff n = FixedPoints.charpolyCoeff G (x : R) n := by
      apply Subtype.ext
      change (FixedPoints.subring R G).subtype (p.coeff n) =
        (MulSemiringAction.charpoly G (x : R)).coeff n
      rw [← Polynomial.coeff_map, hp]
    have hmonic : p.Monic := (Polynomial.monic_X_sub_C x).pow _
    have hdegree : p.natDegree = Fintype.card G := by
      rw [Polynomial.Monic.natDegree_pow (Polynomial.monic_X_sub_C x),
        Polynomial.natDegree_X_sub_C, mul_one]
    have hq : p.map (Ideal.Quotient.mk J) = Polynomial.X ^ Fintype.card G := by
      ext n
      rw [Polynomial.coeff_map, Polynomial.coeff_X_pow]
      rcases lt_trichotomy n (Fintype.card G) with hn | rfl | hn
      · rw [if_neg hn.ne]
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        rw [hcoeff]
        exact FixedPoints.charpolyCoeff_mem G J hxI hn
      · rw [if_pos rfl, ← hdegree, hmonic.coeff_natDegree, map_one]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hdegree.trans_lt hn),
          map_zero, if_neg hn.ne']
    simpa only [p, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, hx, Nat.card_eq_fintype_card] using hq

/-- The fixed-subring quotient map is shift-power generated. -/
@[stacks 0H35 "shift-power generation of the fixed-subring quotient map"]
theorem isGenerated (J : Ideal (FixedPoints.subring R G)) [Finite G] :
    RingHom.ShiftPower.IsGenerated (map J) := by
  apply top_unique
  intro b _
  apply Subring.subset_closure
  right
  obtain ⟨P, _, hP⟩ := exists_monic J b
  exact ⟨Nat.card G, Nat.card_pos, P, hP⟩

/-- The fixed-subring quotient map is integral. -/
@[stacks 0H35 "integrality of the fixed-subring quotient map"]
theorem isIntegral (J : Ideal (FixedPoints.subring R G)) [Finite G] :
    (map J).IsIntegral := by
  intro b
  obtain ⟨P, hP, hPb⟩ := exists_monic J b
  refine ⟨P, hP, ?_⟩
  rw [← Polynomial.eval_map, hPb]
  simp [Nat.ne_of_gt (Nat.card_pos (α := G))]

end FixedPoints.Quotient
