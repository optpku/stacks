module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Galois.IntegralClosure
public import ReasLib.FieldTheory.Galois.IntegralClosure.ResidueField
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.RingTheory.LocalRing.Integral
public import ReasLib.RingTheory.Ideal.Cotangent.Inertia.ResidueField
public import ReasLib.RingTheory.Invariant.ResidueField.RootsOfUnity
public import ReasLib.RingTheory.RootsOfUnity.Power

@[expose] public section

/-!
# Tame inertia of a finite Galois extension

For a maximal branch `m` of the integral closure of a discrete valuation ring, the determinant of
the inertia action on `m / m²` gives the canonical tame character.  Its kernel is wild inertia and
its image is the group of roots of unity indexed by the ramification index.

The quotient-facing API exposes an explicit forward homomorphism together with injectivity and
surjectivity.  It deliberately does not choose an inverse from those proof obligations.

@stack 09EE
@stack 0BU3
@stack 0BU4
@stack 0BU5
@stack 0BU8
-/

universe u v w

namespace integralClosure.Tame

open scoped Pointwise

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type w} [Field L] [Algebra A L] [Algebra K L]
variable [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]

/-- The residue-field determinant of inertia has order dividing the ramification index. -/
@[stacks 09EE "tame inertia determinant has ramification order"]
theorem det_mem_roots (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (σ : m.inertia Gal(L/K)) :
    Ideal.Cotangent.residueDet m σ ∈
      rootsOfUnity (Ideal.ramificationIdxIn (IsLocalRing.maximalIdeal A)
        (integralClosure A L)) m.ResidueField := sorry
-- Proof strategy: raise `σ` to the cardinality of its finite inertia group, apply the monoid hom
-- `Ideal.Cotangent.residueDet m`, and rewrite that cardinality with
-- `Ideal.card_inertia_eq_ramificationIdxIn`; finish with `mem_rootsOfUnity`.

/-- The tame quotient determinant has order dividing the ramification index. -/
@[stacks 09EE "tame quotient determinant has ramification order"]
theorem tameDet_mem_roots (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (τ : m.tameInertia Gal(L/K)) :
    Ideal.Cotangent.tameResidueDet m τ ∈
      rootsOfUnity (Ideal.ramificationIdxIn (IsLocalRing.maximalIdeal A)
        (integralClosure A L)) m.ResidueField := sorry
-- Proof strategy: choose an inertia representative of `τ` with
-- `QuotientGroup.mk'_surjective`, rewrite by `Ideal.Cotangent.tameResidueDet_mk`, and apply
-- `det_mem_roots` to that representative.

/-- The explicit map from tame inertia to roots of unity induced by the tame quotient determinant. -/
@[stacks 09EE, stacks 0BU3, stacks 0BU4 "tame inertia quotient homomorphism"]
noncomputable def quotientHom (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    m.tameInertia Gal(L/K) →*
      rootsOfUnity (Ideal.ramificationIdxIn (IsLocalRing.maximalIdeal A)
        (integralClosure A L)) m.ResidueField :=
  Ideal.Cotangent.tameResidueDetRoots m
    (Ideal.ramificationIdxIn (IsLocalRing.maximalIdeal A) (integralClosure A L))
    (tameDet_mem_roots (K := K) m)

/-- The canonical tame inertia character induced by the quotient homomorphism. -/
@[stacks 09EE, stacks 0BU3, stacks 0BU4 "canonical tame inertia character"]
noncomputable def character (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    m.inertia Gal(L/K) →*
      rootsOfUnity (Ideal.ramificationIdxIn (IsLocalRing.maximalIdeal A)
        (integralClosure A L)) m.ResidueField :=
  (quotientHom (K := K) m).comp
    (QuotientGroup.mk'
      ((m.wildInertia Gal(L/K)).subgroupOf (m.inertia Gal(L/K))))

/-- The tame character has the residue-field determinant as its underlying unit. -/
@[simp, stacks 09EE "tame inertia character evaluation"]
theorem character_coe_apply (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (σ : m.inertia Gal(L/K)) :
    (character (K := K) m σ : m.ResidueFieldˣ) =
      Ideal.Cotangent.residueDet m σ := sorry
-- Proof strategy: unfold `character` and `quotientHom`, then use
-- `Ideal.Cotangent.tameResidueDetRoots_mk`; coercing the codomain restriction exposes the
-- underlying residue determinant.

/-- The kernel of the tame character is wild inertia inside inertia. -/
@[stacks 09EE, stacks 0BU4 "kernel of the tame inertia character"]
theorem character_ker (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    (character (K := K) m).ker =
      (m.wildInertia Gal(L/K)).subgroupOf (m.inertia Gal(L/K)) := sorry
-- Proof strategy: characterize membership in the kernel through `character_coe_apply`.  Use that
-- the branch cotangent space is one-dimensional over the residue field, so determinant one is
-- equivalent to the identity cotangent action, and conclude with
-- `Ideal.Cotangent.inertiaRepresentation_ker`.

/-- The tame character is surjective onto the roots of unity indexed by the ramification index. -/
@[stacks 09EE, stacks 0BU4 "surjectivity of the tame inertia character"]
theorem character_surjective (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    Function.Surjective (character (K := K) m) := sorry
-- Proof strategy: identify the image of `character` with the finite cyclic subgroup generated by
-- the cotangent action.  Compare its cardinality with the ramification index using
-- `Ideal.card_inertia_eq_ramificationIdxIn` and `character_ker`, then use the roots-of-unity card
-- bound to show that this image is the full stated subgroup.

/-- The tame inertia quotient is cyclic. -/
@[stacks 09EE "cyclic tame inertia quotient"]
theorem tameInertia_isCyclic (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    IsCyclic (m.tameInertia Gal(L/K)) := sorry
-- Proof strategy: use `character_ker` and the first isomorphism theorem to identify tame inertia
-- with the range of `character`; that range is a subgroup of the cyclic group of roots of unity,
-- so inherit cyclicity with `Subgroup.isCyclic_of_le`.

/-- The residue characteristic of a maximal branch agrees with that of the base branch. -/
@[stacks 09EE "base and branch residue characteristics agree"]
theorem ringChar_eq_base (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    ringChar m.ResidueField =
      ringChar (IsLocalRing.maximalIdeal A).ResidueField := sorry
-- Proof strategy: install `integralClosure.ResidueField.algebraOfBase m`; its algebra map between
-- fields is injective, so apply the standard characteristic-transport theorem for an injective
-- ring hom and orient the resulting equality as stated.

/-- The mod-square congruence subgroup agrees with wild inertia when the branch residue field is
separable over the base residue field. -/
@[stacks 09EE "separable residue-field mod-square wild inertia bridge"]
theorem modSquareInertia_eq_wildInertia_of_isSeparable
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (hsep :
      -- Local instance justification (defeq pin): select the canonical base-to-branch residue algebra used by the separability predicate.
      letI : Algebra (IsLocalRing.maximalIdeal A).ResidueField m.ResidueField :=
        integralClosure.ResidueField.algebraOfBase m
      Algebra.IsSeparable
        (IsLocalRing.maximalIdeal A).ResidueField m.ResidueField) :
    m.modSquareInertia Gal(L/K) = m.wildInertia Gal(L/K) := sorry
-- Proof strategy: one inclusion is `Ideal.modSquareInertia_le_wildInertia`.  For the converse,
-- combine trivial residue action with the wild cotangent condition; separability kills the
-- resulting residue derivation, upgrading triviality on `m / m ^ 2` to triviality on the full
-- quotient by `m ^ 2`.

/-- In positive residue characteristic, wild inertia is a group at the residue characteristic. -/
@[stacks 09EE "wild inertia p-group"]
theorem wildInertia_isPGroup_of_char_ne_zero
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (hchar : ringChar (IsLocalRing.maximalIdeal A).ResidueField ≠ 0) :
    IsPGroup (ringChar (IsLocalRing.maximalIdeal A).ResidueField)
      (m.wildInertia Gal(L/K)) := sorry
-- Proof strategy: use `ringChar_eq_base` to work in the branch residue characteristic.  Filter
-- wild inertia by its action on successive powers of `m`; each graded quotient embeds in an
-- additive group over the characteristic-`p` residue field, and finite induction shows every
-- element has `p`-power order.  Apply `IsPGroup.iff_orderOf`.

/-- In residue characteristic zero, wild inertia is trivial. -/
@[stacks 09EE "wild inertia trivial in characteristic zero"]
theorem wildInertia_eq_bot_of_char_zero
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (hchar : ringChar (IsLocalRing.maximalIdeal A).ResidueField = 0) :
    m.wildInertia Gal(L/K) = ⊥ := sorry
-- Proof strategy: transport characteristic zero to the branch with `ringChar_eq_base`.  The
-- associated-graded characterization makes every wild element a finite-order unipotent action
-- on a characteristic-zero DVR filtration; the only such element is the identity.  Conclude by
-- subgroup extensionality.

/-- In positive residue characteristic, tame inertia has order prime to the residue characteristic. -/
@[stacks 09EE "tame inertia prime-to-characteristic order"]
theorem tameInertiaCard_coprime_ringChar
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (hchar : ringChar (IsLocalRing.maximalIdeal A).ResidueField ≠ 0) :
    Nat.Coprime (Nat.card (m.tameInertia Gal(L/K)))
      (ringChar (IsLocalRing.maximalIdeal A).ResidueField) := sorry
-- Proof strategy: identify tame inertia with the image of `character` using `character_ker`.
-- This finite image lies in the multiplicative group of the branch residue field, whose finite
-- subgroups have order prime to its positive characteristic; transport the characteristic with
-- `ringChar_eq_base`.

/-- The tame inertia order is either in residue characteristic zero or prime to that
characteristic. -/
@[stacks 09EE "tame inertia characteristic dichotomy"]
theorem tameInertiaCard_coprime_or_char_zero
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    ringChar (IsLocalRing.maximalIdeal A).ResidueField = 0 ∨
      Nat.Coprime (Nat.card (m.tameInertia Gal(L/K)))
        (ringChar (IsLocalRing.maximalIdeal A).ResidueField) := sorry
-- Proof strategy: split on whether the base residue characteristic is zero; return the left
-- disjunct in that case and apply `tameInertiaCard_coprime_ringChar` otherwise.

/-- The tame inertia order is the prime-to-residue-characteristic part of the ramification
index. In residue characteristic zero, `ordCompl[0] e = e`. -/
@[stacks 09EE "tame inertia has the prime-to-characteristic ramification order"]
theorem tameInertiaCard_eq_ordCompl_ramificationIdx
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    Nat.card (m.tameInertia Gal(L/K)) =
      ordCompl[ringChar (IsLocalRing.maximalIdeal A).ResidueField]
        (Ideal.ramificationIdxIn (IsLocalRing.maximalIdeal A)
          (integralClosure A L)) := sorry
-- Proof strategy: use `Ideal.card_inertia_eq_ramificationIdxIn` and the cardinality formula for
-- the exact quotient `Ideal.tameExtension m`.  In positive characteristic the wild factor is a
-- power of `p` by `wildInertia_isPGroup_of_char_ne_zero` and the tame factor is coprime to `p`;
-- in characteristic zero use `wildInertia_eq_bot_of_char_zero`.  Finish with the defining
-- arithmetic properties of `Nat.ordCompl`.

/-- The tame inertia character is equivariant for decomposition-group conjugation on roots of
unity in the residue field. -/
@[stacks 0BU5 "tame inertia character conjugation"]
theorem character_conj_compatible
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (τ : MulAction.stabilizer Gal(L/K) m)
    (σ : m.inertia Gal(L/K)) :
    character (K := K) m (Ideal.inertiaConjHom m τ σ) =
      (Ideal.ResidueField.Invariant.rootsOfUnityHom Gal(L/K)
        (IsLocalRing.maximalIdeal A) m
        (Ideal.ramificationIdxIn (IsLocalRing.maximalIdeal A)
          (integralClosure A L)) τ)
        (character (K := K) m σ) := sorry
-- Proof strategy: coerce both roots of unity to residue-field units, rewrite the left side with
-- `character_coe_apply` and `Ideal.inertiaConjHom_apply`, and use naturality of the determinant
-- under conjugation.  Rewrite the right action with
-- `Ideal.ResidueField.Invariant.rootsOfUnityHom_apply`.

/-- The quotient homomorphism agrees with the tame character on inertia classes. -/
@[simp, stacks 09EE, stacks 0BU3 "tame inertia quotient map evaluation"]
theorem quotientHom_mk (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (σ : m.inertia Gal(L/K)) :
    quotientHom (K := K) m (QuotientGroup.mk σ) = character (K := K) m σ := sorry
-- Proof strategy: unfold `character`; it is definitionally `quotientHom` composed with the
-- quotient map, so reduce the two bundled monoid-hom evaluations.

/-- The forward homomorphism from tame inertia to roots of unity is injective. -/
@[stacks 09EE "injectivity of the tame inertia quotient map"]
theorem quotientHom_injective (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    Function.Injective (quotientHom (K := K) m) := sorry
-- Proof strategy: choose inertia representatives for two quotient classes.  Rewrite equality of
-- their images with `quotientHom_mk`; `character_ker` says their quotient lies in wild inertia,
-- which is exactly equality in the quotient group.

/-- The forward homomorphism from tame inertia to roots of unity is surjective. -/
@[stacks 09EE "surjectivity of the tame inertia quotient map"]
theorem quotientHom_surjective (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    Function.Surjective (quotientHom (K := K) m) := sorry
-- Proof strategy: lift a target through `character_surjective`, then take the quotient class of
-- the resulting inertia element and rewrite its image with `quotientHom_mk`.

/-- The explicit tame-inertia quotient map is bijective. -/
@[stacks 09EE, stacks 0BU3, stacks 0BU4
  "canonical identification of tame inertia with roots of unity"]
theorem quotientHom_bijective (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    Function.Bijective (quotientHom (K := K) m) := sorry
-- Proof strategy: pair `quotientHom_injective m` with `quotientHom_surjective m`.

/-- The tame inertia order divides the ramification index of the maximal branch. -/
@[stacks 09EE "tame inertia order divides ramification index"]
theorem tameInertiaCard_dvd_ramificationIdx
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    Nat.card (m.tameInertia Gal(L/K)) ∣
      Ideal.ramificationIdxIn (IsLocalRing.maximalIdeal A)
        (integralClosure A L) := sorry
-- Proof strategy: rewrite the tame cardinality with
-- `tameInertiaCard_eq_ordCompl_ramificationIdx` and apply `Nat.ordCompl_dvd`.

/-- The order of the tame inertia quotient at a maximal branch. -/
@[stacks 0BU8 "tame inertia quotient order"]
noncomputable abbrev tameCard (m : Ideal (integralClosure A L)) [m.IsMaximal] : ℕ :=
  Nat.card (m.tameInertia Gal(L/K))

/-- The wild scaling factor in the ramification index. -/
@[stacks 0BU8 "wild scaling factor"]
noncomputable def tameScale (m : Ideal (integralClosure A L)) [m.IsMaximal] : ℕ :=
  Ideal.ramificationIdxIn (IsLocalRing.maximalIdeal A) (integralClosure A L) /
    tameCard (K := K) m

/-- The canonical scaled tame inertia character. -/
@[stacks 0BU8 "scaled tame inertia character"]
noncomputable def scaledCharacter
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    m.inertia Gal(L/K) →* rootsOfUnity (tameCard (K := K) m) m.ResidueField :=
  (rootsOfUnity.powMap
      (tameInertiaCard_dvd_ramificationIdx (K := K) m)).comp
    (character (K := K) m)

/-- The scaled character is powering by the wild factor on underlying residue-field units. -/
@[simp, stacks 0BU8 "scaled tame character evaluation"]
theorem scaledCharacter_coe_apply
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (σ : m.inertia Gal(L/K)) :
    (scaledCharacter (K := K) m σ : Units m.ResidueField) =
      (character (K := K) m σ : Units m.ResidueField) ^ tameScale (K := K) m := sorry
-- Proof strategy: unfold `scaledCharacter` and `tameScale`, then apply
-- `rootsOfUnity.powMap_coe_apply` to the divisibility proof
-- `tameInertiaCard_dvd_ramificationIdx`.

/-- The scaled character on the tame quotient, before passing to the quotient isomorphism. -/
@[stacks 0BU8 "scaled tame quotient map"]
noncomputable def scaledQuotientMap
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    m.tameInertia Gal(L/K) →* rootsOfUnity (tameCard (K := K) m) m.ResidueField :=
  (rootsOfUnity.powMap
      (tameInertiaCard_dvd_ramificationIdx (K := K) m)).comp
    (quotientHom (K := K) m)

/-- The scaled quotient map evaluates on a quotient class as the scaled character. -/
@[simp, stacks 0BU8 "scaled quotient map on inertia classes"]
theorem scaledQuotientMap_mk
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (σ : m.inertia Gal(L/K)) :
    scaledQuotientMap (K := K) m (QuotientGroup.mk σ) =
      scaledCharacter (K := K) m σ := sorry
-- Proof strategy: unfold the two scaled maps, rewrite the inner quotient map with
-- `quotientHom_mk`, and reduce composition of bundled monoid homomorphisms.

/-- The scaled quotient map is bijective onto the roots of unity of tame order. -/
@[stacks 0BU8 "scaled tame quotient map bijective"]
theorem scaledQuotientMap_bijective
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    Function.Bijective (scaledQuotientMap (K := K) m) := sorry
-- Proof strategy: combine `quotientHom_bijective` with bijectivity of the roots-of-unity power
-- map.  The exponent is the residue-characteristic part of the ramification index, hence is
-- coprime to the tame roots group by `tameInertiaCard_coprime_or_char_zero`; use the standard
-- power automorphism criterion for a finite cyclic group.

/-- The scaled character has wild inertia as its kernel. -/
@[stacks 0BU8 "scaled tame character kernel"]
theorem scaledCharacter_ker
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    (scaledCharacter (K := K) m).ker =
      (m.wildInertia Gal(L/K)).subgroupOf (m.inertia Gal(L/K)) := sorry
-- Proof strategy: factor `scaledCharacter` as `scaledQuotientMap` after the quotient projection.
-- Since `scaledQuotientMap_bijective` gives injectivity, the composite kernel is the kernel of
-- `QuotientGroup.mk'`, namely the wild inertia subgroup.

/-- The scaled character is surjective onto the roots of unity of tame order. -/
@[stacks 0BU8 "scaled tame character surjective"]
theorem scaledCharacter_surjective
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    Function.Surjective (scaledCharacter (K := K) m) := sorry
-- Proof strategy: compose surjectivity of `QuotientGroup.mk'` with the surjective component of
-- `scaledQuotientMap_bijective`, using `scaledQuotientMap_mk` for the composite formula.

/-- The ramification index is the tame order times the wild scaling factor. -/
@[stacks 0BU8 "ramification index tame-wild factorization"]
theorem tameScale_spec
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    Ideal.ramificationIdxIn (IsLocalRing.maximalIdeal A) (integralClosure A L) =
        tameScale (K := K) m * tameCard (K := K) m ∧
      (ringChar m.ResidueField = 0 → tameScale (K := K) m = 1) ∧
      (ringChar m.ResidueField ≠ 0 →
        ∃ s : ℕ, tameScale (K := K) m = ringChar m.ResidueField ^ s) := sorry
-- Proof strategy: unfold `tameScale` and rewrite `tameCard` using
-- `tameInertiaCard_eq_ordCompl_ramificationIdx`.  Apply
-- `Nat.ordProj_mul_ordCompl_eq_self` for the factorization.  In characteristic zero simplify
-- `ordCompl[0]`; otherwise use primality of the residue characteristic and the definition of
-- `Nat.ordProj` to obtain the displayed power, transporting base/branch characteristic with
-- `ringChar_eq_base`.

/-- The ramification index factors as the wild scale times the tame order. -/
@[stacks 0BU8 "ramification index factorization by tame order"]
theorem ramificationIdxIn_eq_tameScale_mul_tameCard
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    Ideal.ramificationIdxIn (IsLocalRing.maximalIdeal A) (integralClosure A L) =
      tameScale (K := K) m * tameCard (K := K) m := sorry
-- Proof strategy: project the first component of `tameScale_spec m`.

/-- In residue characteristic zero the wild scale is one. -/
@[stacks 0BU8 "wild scale in residue characteristic zero"]
theorem tameScale_eq_one_of_char_zero
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (hchar : ringChar m.ResidueField = 0) :
    tameScale (K := K) m = 1 := sorry
-- Proof strategy: apply the characteristic-zero implication in the second component of
-- `tameScale_spec m` to `hchar`.

/-- In positive residue characteristic the wild scale is a power of that characteristic. -/
@[stacks 0BU8 "wild scale is a residue-characteristic power"]
theorem tameScale_eq_char_pow_of_char_ne_zero
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (hchar : ringChar m.ResidueField ≠ 0) :
    ∃ s : ℕ, tameScale (K := K) m = ringChar m.ResidueField ^ s := sorry
-- Proof strategy: apply the positive-characteristic implication in `tameScale_spec m` to
-- `hchar`.

/-- The roots of unity indexed by the ramification index equal those indexed by tame inertia. -/
@[stacks 0BU8 "ramification roots equal tame roots"]
theorem rootsOfUnity_eq_tameCard
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    rootsOfUnity
        (Ideal.ramificationIdxIn (IsLocalRing.maximalIdeal A) (integralClosure A L))
        m.ResidueField =
      rootsOfUnity (tameCard (K := K) m) m.ResidueField := sorry
-- Proof strategy: use `ramificationIdxIn_eq_tameScale_mul_tameCard`.  In characteristic zero the
-- scale is one; in positive characteristic it is a power of the field characteristic, whose
-- only root-of-unity contribution is trivial.  Prove both subgroup inclusions via
-- `mem_rootsOfUnity` and the corresponding power identities.

/-- The canonical decomposition-group action on the scaled character is by conjugation. -/
@[stacks 0BU8 "scaled tame character conjugation"]
theorem scaledCharacter_conj_compatible
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (τ : MulAction.stabilizer Gal(L/K) m)
    (σ : m.inertia Gal(L/K)) :
    scaledCharacter (K := K) m (Ideal.inertiaConjHom m τ σ) =
      (Ideal.ResidueField.Invariant.rootsOfUnityHom Gal(L/K)
        (IsLocalRing.maximalIdeal A) m (tameCard (K := K) m) τ)
        (scaledCharacter (K := K) m σ) := sorry
-- Proof strategy: unfold `scaledCharacter`, apply `character_conj_compatible`, and use that the
-- residue-field automorphism action commutes with taking the fixed natural-number power in
-- `rootsOfUnity.powMap`; finish with `rootsOfUnityHom_apply`.

end integralClosure.Tame
