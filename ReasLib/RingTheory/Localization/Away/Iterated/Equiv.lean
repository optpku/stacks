/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.Away.Iterated

/-!
# Canonical Equivalence for Iterated Principal Localizations

This leaf identifies the localization of `Localization.Away a` away from the
image of `b` with `Localization.Away (a * b)`.  The target uses the named
right-handed algebra action from `Localization.Away.Iterated.rightAlgebra`.

@stack 051T
-/

@[expose] public section

universe u v

noncomputable section

namespace Localization.Away.Iterated

variable {R : Type u} [CommSemiring R]

/-- The canonical `Localization.Away a`-algebra equivalence from the
coefficient chart obtained by localizing again at the image of `b` to
`Localization.Away (a * b)`. -/
@[stacks 051T "iterated principal-localization coefficient equivalence"]
noncomputable def coefficientEquiv (a b : R) :
    -- Local instance justification (noncanonical choice): the equivalence uses the named right action.
    letI : Algebra (Localization.Away a) (Localization.Away (a * b)) :=
      rightAlgebra a b
    coefficientChart a b ≃ₐ[Localization.Away a] Localization.Away (a * b) :=
  -- Local instance justification (noncanonical choice): retain the named right action.
  letI : Algebra (Localization.Away a) (Localization.Away (a * b)) :=
    rightAlgebra a b
  -- Local instance justification (defeq pin): use the localization proof from the right action.
  letI : IsLocalization.Away (coefficient a b) (Localization.Away (a * b)) :=
    coefficientIsLocalization a b
  IsLocalization.algEquiv (Submonoid.powers (coefficient a b)) _ _

/-- The coefficient-chart equivalence agrees with the two canonical algebra
maps from `Localization.Away a`. -/
@[simp, stacks 051T "iterated principal-localization coefficient equivalence on scalars"]
theorem coefficientEquiv_apply_algebraMap (a b : R) (x : Localization.Away a) :
    -- Local instance justification (noncanonical choice): select the same right action as the equivalence.
    letI : Algebra (Localization.Away a) (Localization.Away (a * b)) :=
      rightAlgebra a b
    coefficientEquiv a b
        (algebraMap (Localization.Away a) (coefficientChart a b) x) =
      algebraMap (Localization.Away a) (Localization.Away (a * b)) x := sorry

/-- The coefficient-chart equivalence sends a localization representative to
the representative with the same numerator and denominator in the product
localization. -/
@[simp, stacks 051T "iterated principal-localization coefficient equivalence on representatives"]
theorem coefficientEquiv_apply_mk' (a b : R) (x : Localization.Away a)
    (y : Submonoid.powers (coefficient a b)) :
    -- Local instance justification (noncanonical choice): select the named right action.
    letI : Algebra (Localization.Away a) (Localization.Away (a * b)) :=
      rightAlgebra a b
    -- Local instance justification (defeq pin): use the matching localization proof.
    letI : IsLocalization.Away (coefficient a b) (Localization.Away (a * b)) :=
      coefficientIsLocalization a b
    coefficientEquiv a b (IsLocalization.mk' (coefficientChart a b) x y) =
      IsLocalization.mk' (Localization.Away (a * b)) x y := sorry

/-- The inverse coefficient-chart equivalence sends a product-localization
representative back to the representative with the same numerator and
denominator in the iterated chart. -/
@[simp, stacks 051T "inverse iterated principal-localization coefficient equivalence"]
theorem coefficientEquiv_symm_apply_mk' (a b : R) (x : Localization.Away a)
    (y : Submonoid.powers (coefficient a b)) :
    -- Local instance justification (noncanonical choice): select the named right action.
    letI : Algebra (Localization.Away a) (Localization.Away (a * b)) :=
      rightAlgebra a b
    -- Local instance justification (defeq pin): use the matching localization proof.
    letI : IsLocalization.Away (coefficient a b) (Localization.Away (a * b)) :=
      coefficientIsLocalization a b
    (coefficientEquiv a b).symm
        (IsLocalization.mk' (Localization.Away (a * b)) x y) =
      IsLocalization.mk' (coefficientChart a b) x y := sorry

end Localization.Away.Iterated

namespace Localization.Away

variable {R : Type u} [CommSemiring R]

/-- Reindex a principal localization algebra along an equality of its
distinguished denominators. -/
@[stacks 051T "principal-localization denominator algebra equivalence"]
noncomputable def denominatorEquiv {a b : R} (h : a = b) :
    Localization.Away a ≃ₐ[R] Localization.Away b :=
  h.rec (AlgEquiv.refl)

/-- Denominator reindexing agrees with the canonical coefficient maps. -/
@[simp, stacks 051T "principal-localization denominator algebra equivalence on coefficients"]
theorem denominatorEquiv_apply_algebraMap {a b : R} (h : a = b) (r : R) :
    denominatorEquiv h (algebraMap R (Localization.Away a) r) =
      algebraMap R (Localization.Away b) r := sorry

variable {S : Type v} [CommSemiring S]

/-- The canonical map on product principal localizations induced by a ring
homomorphism.  Its codomain is indexed by `φ a * φ b`, the denominator shape
used by pairwise gluing overlaps. -/
@[stacks 05EQ "product principal-localization base-change map"]
noncomputable def productMap (φ : R →+* S) (a b : R) :
    Localization.Away (a * b) →+* Localization.Away (φ a * φ b) :=
  (denominatorEquiv (map_mul φ a b)).toRingHom.comp
    (Localization.awayMap φ (a * b))

/-- The product principal-localization map agrees with the canonical
coefficient maps. -/
@[simp, stacks 05EQ "product principal-localization base-change map on coefficients"]
theorem productMap_apply_algebraMap (φ : R →+* S) (a b r : R) :
    productMap φ a b (algebraMap R (Localization.Away (a * b)) r) =
      algebraMap S (Localization.Away (φ a * φ b)) (φ r) := sorry

/-- The square formed by a ring map and the two coefficient maps into product
principal localizations commutes. -/
@[stacks 05EQ "product principal-localization base-change square"]
theorem productMap_comp_algebraMap (φ : R →+* S) (a b : R) :
    (productMap φ a b).comp
        (algebraMap R (Localization.Away (a * b))) =
      (algebraMap S (Localization.Away (φ a * φ b))).comp φ := sorry

end Localization.Away
