/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Galois.IntegralClosure.Tame
public import ReasLib.FieldTheory.Galois.IntegralClosure.Tower.Inertia

@[expose] public section

/-!
# Tame characters in finite Galois towers

This file owns the functorial maps used to compare tame characters through an integral-closure
tower.  The residue-field map is always the canonical forward map; no inverse or chosen lift is
part of the API.

@stack 0BU7
@stack 0BU8
-/

universe u v w z

namespace integralClosure.Tower.Tame

open Ideal IsLocalRing

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type w} [Field L] [Algebra A L] [Algebra K L]
  [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]
variable {M : Type z} [Field M] [Algebra A M] [Algebra K M] [Algebra L M]
  [IsScalarTower A K M] [IsScalarTower K L M] [IsScalarTower A L M]
  [FiniteDimensional K M] [IsGalois K M]

section Character

/-- The roots-of-unity power map from the upper ramification index to the lower one. -/
@[stacks 0BU7 "tower ramification power map"]
noncomputable def ramificationPower
    (r : Ideal (integralClosure A M)) [r.IsMaximal] :
    rootsOfUnity (Ideal.ramificationIdxIn (maximalIdeal A) (integralClosure A M)) r.ResidueField →*
      rootsOfUnity (Ideal.ramificationIdxIn (maximalIdeal A) (integralClosure A L)) r.ResidueField :=
  rootsOfUnity.powMap
    (integralClosure.Tower.ramificationIdxIn_dvd (A := A) (K := K) (L := L) (M := M))

/-- The underlying unit of the tower ramification power map is the quotient power. -/
@[simp, stacks 0BU7 "tower ramification power map formula"]
theorem ramificationPower_coe_apply
    (r : Ideal (integralClosure A M)) [r.IsMaximal]
    (ζ : rootsOfUnity
      (Ideal.ramificationIdxIn (maximalIdeal A) (integralClosure A M)) r.ResidueField) :
    (ramificationPower (A := A) (K := K) (L := L) (M := M) r ζ : Units r.ResidueField) =
      (ζ : Units r.ResidueField) ^
        (Ideal.ramificationIdxIn (maximalIdeal A) (integralClosure A M) /
          Ideal.ramificationIdxIn (maximalIdeal A) (integralClosure A L)) := sorry
-- Proof strategy: unfold `ramificationPower` and apply `rootsOfUnity.powMap_coe_apply` to
-- `integralClosure.Tower.ramificationIdxIn_dvd`.

/-- The lower tame character, transported to the upper residue field. -/
@[stacks 0BU7 "lower tame character transported to the upper residue field"]
noncomputable def baseCharacter
    (r : Ideal (integralClosure A M)) [r.IsMaximal] :
    (integralClosure.Tower.under (A := A) (L := L) (M := M) r).inertia Gal(L / K) →*
      rootsOfUnity (Ideal.ramificationIdxIn (maximalIdeal A) (integralClosure A L)) r.ResidueField :=
  (restrictRootsOfUnity
      (integralClosure.Tower.residueMap (A := A) (L := L) (M := M) r)
      (Ideal.ramificationIdxIn (maximalIdeal A) (integralClosure A L))).comp
    (integralClosure.Tame.character (K := K)
      (integralClosure.Tower.under (A := A) (L := L) (M := M) r))

/-- The unscaled tame character commutes with inertia restriction and residue-field transport. -/
@[stacks 0BU7 "naturality of the tame character in a tower"]
theorem character_naturality
    (r : Ideal (integralClosure A M)) [r.IsMaximal] :
    (baseCharacter (A := A) (K := K) (L := L) (M := M) r).comp
        (integralClosure.Tower.inertiaHom (A := A) (K := K) (L := L) (M := M) r) =
      (ramificationPower (A := A) (K := K) (L := L) (M := M) r).comp
        (integralClosure.Tame.character (K := K) r) := sorry
-- Proof strategy: ext an upper inertia element and coerce both roots of unity to residue-field
-- units. Rewrite the characters by `integralClosure.Tame.character_coe_apply`, restriction by
-- `integralClosure.Tower.inertiaHom_apply`, residue transport by `residueMap_algebraMap`, and the
-- right side by `ramificationPower_coe_apply`; the remaining equality is the tower formula for
-- the cotangent determinant (equivalently the compatible-uniformizer calculation).

/-- Pointwise form of tame-character naturality in a tower. -/
@[simp, stacks 0BU7 "pointwise tame character naturality in a tower"]
theorem character_naturality_apply
    (r : Ideal (integralClosure A M)) [r.IsMaximal]
    (σ : r.inertia Gal(M / K)) :
    baseCharacter (A := A) (K := K) (L := L) (M := M) r
        (integralClosure.Tower.inertiaHom (A := A) (K := K) (L := L) (M := M) r σ) =
      ramificationPower (A := A) (K := K) (L := L) (M := M) r
        (integralClosure.Tame.character (K := K) r σ) := sorry
-- Proof strategy: apply `DFunLike.congr_fun` to `character_naturality r` and reduce both
-- `MonoidHom.comp` evaluations.

/-- The lower quotient character, transported to the upper residue field. -/
@[stacks 0BU7 "lower tame quotient map transported to the upper residue field"]
noncomputable def baseQuotientHom
    (r : Ideal (integralClosure A M)) [r.IsMaximal] :
    (integralClosure.Tower.under (A := A) (L := L) (M := M) r).tameInertia Gal(L / K) →*
      rootsOfUnity (Ideal.ramificationIdxIn (maximalIdeal A) (integralClosure A L)) r.ResidueField :=
  (restrictRootsOfUnity
      (integralClosure.Tower.residueMap (A := A) (L := L) (M := M) r)
      (Ideal.ramificationIdxIn (maximalIdeal A) (integralClosure A L))).comp
    (integralClosure.Tame.quotientHom (K := K)
      (integralClosure.Tower.under (A := A) (L := L) (M := M) r))

/-- The tame quotient maps commute with restriction in a tower. -/
@[stacks 0BU7 "naturality of the tame quotient map in a tower"]
theorem quotientHom_naturality
    (r : Ideal (integralClosure A M)) [r.IsMaximal] :
    (baseQuotientHom (A := A) (K := K) (L := L) (M := M) r).comp
        (integralClosure.Tower.tameInertiaHom (A := A) (K := K) (L := L) (M := M) r) =
      (ramificationPower (A := A) (K := K) (L := L) (M := M) r).comp
        (integralClosure.Tame.quotientHom (K := K) r) := sorry
-- Proof strategy: ext a tame quotient class and use `QuotientGroup.mk'_surjective` to choose an
-- inertia representative. Rewrite the induced restriction with `tameInertiaHom_mk`, both
-- quotient characters with `integralClosure.Tame.quotientHom_mk`, and finish with
-- `character_naturality_apply`.

end Character

section Scaled

/-- The roots-of-unity power map from the upper tame order to the lower tame order. -/
@[stacks 0BU8 "tower tame-order power map"]
noncomputable def tamePower
    (r : Ideal (integralClosure A M)) [r.IsMaximal] :
    rootsOfUnity (integralClosure.Tame.tameCard (K := K) r) r.ResidueField →*
      rootsOfUnity (integralClosure.Tame.tameCard (K := K)
        (integralClosure.Tower.under (A := A) (L := L) (M := M) r)) r.ResidueField :=
  rootsOfUnity.powMap
    (integralClosure.Tower.tameInertiaCard_dvd
      (A := A) (K := K) (L := L) (M := M) r)

/-- The underlying unit of the tame-order power map is the quotient power. -/
@[simp, stacks 0BU8 "tower tame-order power map formula"]
theorem tamePower_coe_apply
    (r : Ideal (integralClosure A M)) [r.IsMaximal]
    (ζ : rootsOfUnity (integralClosure.Tame.tameCard (K := K) r) r.ResidueField) :
    (tamePower (A := A) (K := K) (L := L) (M := M) r ζ : Units r.ResidueField) =
      (ζ : Units r.ResidueField) ^
        (integralClosure.Tame.tameCard (K := K) r /
          integralClosure.Tame.tameCard (K := K)
            (integralClosure.Tower.under (A := A) (L := L) (M := M) r)) := sorry
-- Proof strategy: unfold `tamePower` and apply `rootsOfUnity.powMap_coe_apply` to
-- `integralClosure.Tower.tameInertiaCard_dvd`.

/-- The lower scaled tame character, transported to the upper residue field. -/
@[stacks 0BU8 "lower scaled tame character transported to the upper residue field"]
noncomputable def baseScaledCharacter
    (r : Ideal (integralClosure A M)) [r.IsMaximal] :
    (integralClosure.Tower.under (A := A) (L := L) (M := M) r).inertia Gal(L / K) →*
      rootsOfUnity (integralClosure.Tame.tameCard (K := K)
        (integralClosure.Tower.under (A := A) (L := L) (M := M) r)) r.ResidueField :=
  (restrictRootsOfUnity
      (integralClosure.Tower.residueMap (A := A) (L := L) (M := M) r)
      (integralClosure.Tame.tameCard (K := K)
        (integralClosure.Tower.under (A := A) (L := L) (M := M) r))).comp
    (integralClosure.Tame.scaledCharacter (K := K)
      (integralClosure.Tower.under (A := A) (L := L) (M := M) r))

/-- The scaled tame characters commute with inertia restriction in a tower. -/
@[stacks 0BU8 "naturality of the scaled tame character in a tower"]
theorem scaledCharacter_naturality
    (r : Ideal (integralClosure A M)) [r.IsMaximal] :
    (baseScaledCharacter (A := A) (K := K) (L := L) (M := M) r).comp
        (integralClosure.Tower.inertiaHom (A := A) (K := K) (L := L) (M := M) r) =
      (tamePower (A := A) (K := K) (L := L) (M := M) r).comp
        (integralClosure.Tame.scaledCharacter (K := K) r) := sorry
-- Proof strategy: unfold `baseScaledCharacter`, `scaledCharacter`, and `tamePower`. Combine
-- `character_naturality` with `rootsOfUnity.powMap_comp`; the exponent identity follows from the
-- ramification-index/tame-card factorizations and the divisibilities used to define the three
-- power maps.

/-- Pointwise form of scaled tame-character naturality in a tower. -/
@[simp, stacks 0BU8 "pointwise scaled tame character naturality in a tower"]
theorem scaledCharacter_naturality_apply
    (r : Ideal (integralClosure A M)) [r.IsMaximal]
    (σ : r.inertia Gal(M / K)) :
    baseScaledCharacter (A := A) (K := K) (L := L) (M := M) r
        (integralClosure.Tower.inertiaHom (A := A) (K := K) (L := L) (M := M) r σ) =
      tamePower (A := A) (K := K) (L := L) (M := M) r
        (integralClosure.Tame.scaledCharacter (K := K) r σ) := sorry
-- Proof strategy: apply `DFunLike.congr_fun` to `scaledCharacter_naturality r` and simplify the
-- evaluations of the two composed monoid homomorphisms.

/-- The lower scaled quotient map, transported to the upper residue field. -/
@[stacks 0BU8 "lower scaled quotient map transported to the upper residue field"]
noncomputable def baseScaledQuotientMap
    (r : Ideal (integralClosure A M)) [r.IsMaximal] :
    (integralClosure.Tower.under (A := A) (L := L) (M := M) r).tameInertia Gal(L / K) →*
      rootsOfUnity (integralClosure.Tame.tameCard (K := K)
        (integralClosure.Tower.under (A := A) (L := L) (M := M) r)) r.ResidueField :=
  (restrictRootsOfUnity
      (integralClosure.Tower.residueMap (A := A) (L := L) (M := M) r)
      (integralClosure.Tame.tameCard (K := K)
        (integralClosure.Tower.under (A := A) (L := L) (M := M) r))).comp
    (integralClosure.Tame.scaledQuotientMap (K := K)
      (integralClosure.Tower.under (A := A) (L := L) (M := M) r))

/-- The scaled quotient maps commute with tame-inertia restriction in a tower. -/
@[stacks 0BU8 "naturality of the scaled quotient map in a tower"]
theorem scaledQuotientMap_naturality
    (r : Ideal (integralClosure A M)) [r.IsMaximal] :
    (baseScaledQuotientMap (A := A) (K := K) (L := L) (M := M) r).comp
        (integralClosure.Tower.tameInertiaHom (A := A) (K := K) (L := L) (M := M) r) =
      (tamePower (A := A) (K := K) (L := L) (M := M) r).comp
        (integralClosure.Tame.scaledQuotientMap (K := K) r) := sorry
-- Proof strategy: ext a quotient class, choose an inertia representative with
-- `QuotientGroup.mk'_surjective`, and rewrite by `tameInertiaHom_mk` and
-- `integralClosure.Tame.scaledQuotientMap_mk`; the resulting pointwise equality is
-- `scaledCharacter_naturality_apply`.

end Scaled

end integralClosure.Tower.Tame
