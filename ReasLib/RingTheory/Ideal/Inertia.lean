module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupExtension.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Invariant.Quotient

@[expose] public section

/-!
# Wild, tame, and decomposition groups of an ideal

Wild inertia is the subgroup of inertia acting trivially on the cotangent module `I / I ^ 2`.
The stronger subgroup acting trivially on all of `R / I ^ 2` is retained separately.  The file
also packages the wild/tame exact sequence and conjugation by the decomposition group.

@stack 09EC
@stack 09EE
@stack 0BU4
@stack 0BU5
@stack 09EH
@stack 0BU6
-/

universe u v

open scoped Pointwise

namespace Ideal

variable {R : Type u} {G : Type v}
variable [Ring R] [Group G] [MulSemiringAction G R]

/-- An inertia element preserves the ideal on which it acts trivially modulo that ideal. -/
@[stacks 09EE "inertia preserves its ideal"]
theorem map_eq_self_of_mem_inertia (I : Ideal R) (sigma : I.inertia G) :
    I.map (MulSemiringAction.toRingHom G R (sigma : G)) = I := sorry

-- Proof strategy: coerce `sigma` to the decomposition group with
-- `Ideal.inertia_le_stabilizer I sigma.2`, unfold the pointwise action on ideals, and identify
-- it with the image under `MulSemiringAction.toRingHom`.

/-- An inertia element sends every element of the ideal back into the ideal. -/
@[stacks 09EE "inertia action on ideal elements"]
theorem smul_mem_of_mem_inertia (I : Ideal R) (sigma : I.inertia G) (x : I) :
    (sigma : G) • (x : R) ∈ I := sorry

-- Proof strategy: rewrite membership using `map_eq_self_of_mem_inertia I sigma`; the translate
-- of `x.2 : x ∈ I` lies in the image ideal by the canonical `Ideal.mem_map_of_mem` witness.

/-- The algebra automorphism attached to an inertia element restricts to an endomorphism of the
ideal.  This is the inclusion form used by quotient and cotangent functoriality. -/
@[stacks 09EE "inertia ideal restriction"]
theorem inertia_le_comap (I : Ideal R) (sigma : I.inertia G) :
    I ≤ I.comap (MulSemiringAction.toAlgEquiv ℤ R (sigma : G)).toAlgHom := sorry

-- Proof strategy: introduce `x ∈ I`, rewrite comap membership as membership of its image, and
-- apply `smul_mem_of_mem_inertia I sigma` to the corresponding subtype element.

/-- The pointwise membership criterion for an ideal inertia subgroup. -/
@[stacks 09EC, stacks 09EE "ideal inertia membership criterion"]
theorem mem_inertia_iff (I : Ideal R) (sigma : G) :
    sigma ∈ I.inertia G ↔ ∀ x : R, sigma • x - x ∈ I := sorry

-- Proof strategy: unfold `Ideal.inertia` to `I.toAddSubgroup.inertia` and use the canonical
-- pointwise membership theorem `AddSubgroup.mem_inertia`.

/-- An automorphism is wild at `I` when it acts trivially both on `R / I` and on the cotangent
module `I / I ^ 2`. -/
@[stacks 09EE "wild inertia element predicate"]
def IsWild (I : Ideal R) (sigma : G) : Prop :=
  sigma ∈ I.inertia G ∧ ∀ x : I, sigma • (x : R) - x ∈ I ^ 2

/-- The identity automorphism is wild at every ideal. -/
@[stacks 09EE "identity belongs to wild inertia"]
theorem isWild_one (I : Ideal R) : I.IsWild (1 : G) := sorry

-- Proof strategy: unfold `IsWild`; use `Subgroup.one_mem` for inertia, then simplify `one_smul`
-- and close the cotangent condition with `Ideal.zero_mem`.

/-- The product of two automorphisms wild at an ideal is wild there. -/
@[stacks 09EE "wild inertia is closed under multiplication"]
theorem isWild_mul (I : Ideal R) {sigma tau : G}
    (hsigma : I.IsWild sigma) (htau : I.IsWild tau) :
    I.IsWild (sigma * tau) := sorry

-- Proof strategy: combine the inertia components by subgroup closure.  For `x : I`, expand
-- `(sigma * tau) • x - x` as the sum of `sigma • (tau • x - x)` and `sigma • x - x`; use that
-- inertia stabilizes `I ^ 2` and then apply the two cotangent hypotheses.

/-- The inverse of an automorphism wild at an ideal is wild there. -/
@[stacks 09EE "wild inertia is closed under inversion"]
theorem isWild_inv (I : Ideal R) {sigma : G} (hsigma : I.IsWild sigma) :
    I.IsWild sigma⁻¹ := sorry

-- Proof strategy: use inversion closure of `I.inertia G`.  Rewrite the inverse displacement as
-- the translate by `sigma⁻¹` of the negative original displacement, and use stability of
-- `I ^ 2` under inertia together with `hsigma.2`.

/-- The wild inertia group consists of inertia elements acting trivially on `I / I ^ 2`. -/
@[stacks 09EE, stacks 0BU4 "wild inertia group"]
def wildInertia (I : Ideal R) (G : Type v) [Group G] [MulSemiringAction G R] :
    Subgroup G where
  carrier := {sigma | I.IsWild sigma}
  one_mem' := isWild_one I
  mul_mem' hsigma htau := isWild_mul I hsigma htau
  inv_mem' hsigma := isWild_inv I hsigma

/-- Membership in wild inertia is the conjunction of inertia and trivial cotangent action. -/
@[stacks 09EE "wild inertia membership"]
theorem mem_wildInertia_iff (I : Ideal R) (sigma : G) :
    sigma ∈ I.wildInertia G ↔
      sigma ∈ I.inertia G ∧ ∀ x : I, sigma • (x : R) - x ∈ I ^ 2 := sorry

-- Proof strategy: unfold `wildInertia` and `IsWild`; membership in the explicitly defined
-- subgroup is definitionally the displayed conjunction.

/-- Wild inertia consists exactly of the decomposition elements acting trivially on every
associated-graded piece `I ^ n / I ^ (n + 1)`. -/
@[stacks 09EE "wild inertia as the associated-graded kernel"]
theorem mem_wildInertia_iff_trivial_on_associatedGraded
    {R : Type u} [CommRing R] {G : Type v} [Group G] [MulSemiringAction G R]
    (I : Ideal R) (sigma : G) :
    sigma ∈ I.wildInertia G ↔
      sigma ∈ MulAction.stabilizer G I ∧
        ∀ (n : ℕ) (x : R), x ∈ I ^ n → sigma • x - x ∈ I ^ (n + 1) := sorry

-- Proof strategy: forward, use `wildInertia_le_stabilizer` and induct on `n`; expand generators
-- of `I ^ (n + 1)` with `Ideal.pow_succ` and the multiplicative action, using the cotangent
-- condition at `n = 1`.  Reverse, specialize the graded condition to `n = 0` for inertia and to
-- `n = 1` for the cotangent condition, then apply `mem_wildInertia_iff`.

/-- The mod-square inertia subgroup consists of automorphisms acting trivially on all of
`R / I ^ 2`.  It agrees with wild inertia only under additional residue-separability hypotheses. -/
@[stacks 09EE "mod-square inertia subgroup"]
abbrev modSquareInertia (I : Ideal R) (G : Type v) [Group G]
    [MulSemiringAction G R] : Subgroup G :=
  (I ^ 2).inertia G

/-- Membership in mod-square inertia is pointwise congruence modulo `I ^ 2`. -/
@[stacks 09EE "mod-square inertia membership"]
theorem mem_modSquareInertia_iff (I : Ideal R) (sigma : G) :
    sigma ∈ I.modSquareInertia G ↔ ∀ x : R, sigma • x - x ∈ I ^ 2 := sorry

-- Proof strategy: unfold `modSquareInertia` and apply `mem_inertia_iff` to the ideal `I ^ 2`.

/-- Mod-square inertia fixes every class of the square-ideal quotient. -/
@[stacks 09EE "mod-square inertia quotient-class membership"]
theorem mem_modSquareInertia_quotient_iff {R : Type u} [CommRing R]
    {G : Type v} [Group G] [MulSemiringAction G R] (I : Ideal R) (sigma : G) :
    sigma ∈ I.modSquareInertia G ↔
      ∀ x : R,
        Ideal.Quotient.mk (I ^ 2) (sigma • x) = Ideal.Quotient.mk (I ^ 2) x := sorry

-- Proof strategy: rewrite membership with `mem_modSquareInertia_iff` and each quotient equality
-- with `Ideal.Quotient.mk_eq_mk_iff_sub_mem`.

/-- Acting trivially on `R / I ^ 2` implies membership in wild inertia. -/
@[stacks 09EE "mod-square inertia lies in wild inertia"]
theorem modSquareInertia_le_wildInertia (I : Ideal R) :
    I.modSquareInertia G ≤ I.wildInertia G := sorry

-- Proof strategy: use `mem_modSquareInertia_iff` and `mem_wildInertia_iff`.  The cotangent
-- condition is unchanged, while inertia modulo `I` follows by composing membership in `I ^ 2`
-- with the standard inclusion `I ^ 2 ≤ I`.

/-- The inertia subgroup stabilizes its defining ideal. -/
@[stacks 09EH "inertia stabilizes its defining ideal"]
theorem inertia_isStable {R : Type u} [CommRing R] {G : Type v} [Group G]
    [MulSemiringAction G R] (I : Ideal R) :
    I.IsStable (I.inertia G) := sorry

-- Proof strategy: for `sigma : I.inertia G`, use `map_eq_self_of_mem_inertia I sigma` and the
-- pointwise-action formula for ideals to prove the defining equality of `Ideal.IsStable`.

/-- The canonical action of inertia on the quotient by its defining ideal. -/
@[reducible, stacks 09EH "inertia action on the ideal quotient"]
def inertiaQuotientAction {R : Type u} [CommRing R] {G : Type v} [Group G]
    [MulSemiringAction G R] (I : Ideal R) :
    MulSemiringAction (I.inertia G) (R ⧸ I) :=
  Ideal.Quotient.action I (inertia_isStable I)

/-- The inertia quotient action sends a representative to the class of its translate. -/
@[simp, stacks 09EH "inertia quotient action on representatives"]
theorem inertiaQuotientAction_mk {R : Type u} [CommRing R] {G : Type v} [Group G]
    [MulSemiringAction G R] (I : Ideal R) (sigma : I.inertia G) (x : R) :
    -- Local instance justification (defeq pin): evaluation uses this ideal's named quotient action.
    letI := inertiaQuotientAction (G := G) I
    sigma • Ideal.Quotient.mk I x = Ideal.Quotient.mk I ((sigma : G) • x) := sorry

-- Proof strategy: unfold `inertiaQuotientAction`, reduce the `MulSemiringAction.compHom`
-- evaluation to `Ideal.Quotient.smulHom`, and finish with `Ideal.Quotient.smulHom_mk`.

/-- Wild inertia is contained in inertia. -/
@[stacks 09EE "wild inertia is contained in inertia"]
theorem wildInertia_le_inertia (I : Ideal R) :
    I.wildInertia G ≤ I.inertia G := sorry

-- Proof strategy: introduce a wild element, rewrite with `mem_wildInertia_iff`, and project the
-- inertia component of the conjunction.

/-- Wild inertia is contained in the decomposition group. -/
@[stacks 09EE "wild inertia is contained in the decomposition group"]
theorem wildInertia_le_stabilizer (I : Ideal R) :
    I.wildInertia G ≤ MulAction.stabilizer G I := sorry

-- Proof strategy: compose `wildInertia_le_inertia I` with Mathlib's
-- `Ideal.inertia_le_stabilizer I`.

/-- Wild inertia, viewed inside inertia, is normal. -/
@[stacks 09EE "wild inertia is normal in inertia"]
instance wildInertia_normal_in_inertia (I : Ideal R) :
    ((I.wildInertia G).subgroupOf (I.inertia G)).Normal := sorry

-- Proof strategy: use `Subgroup.normal_subgroupOf_iff`.  Conjugation by an inertia element
-- preserves `I` and `I ^ 2`; expand the conjugated action on each `x : I` and transport the
-- cotangent condition from `mem_wildInertia_iff`.

/-- Wild inertia, viewed inside the decomposition group, is normal. -/
@[stacks 09EE "wild inertia is normal in the decomposition group"]
instance wildInertia_normal_in_stabilizer (I : Ideal R) :
    ((I.wildInertia G).subgroupOf (MulAction.stabilizer G I)).Normal := sorry

-- Proof strategy: again apply `Subgroup.normal_subgroupOf_iff`.  A decomposition element
-- stabilizes `I` and hence `I ^ 2`; conjugating the two conditions in
-- `mem_wildInertia_iff` therefore preserves wild inertia.

/-- The tame inertia group is the quotient of inertia by wild inertia. -/
@[stacks 09EE, stacks 0BU4 "tame inertia group"]
abbrev tameInertia (I : Ideal R) (G : Type v) [Group G] [MulSemiringAction G R] :=
  I.inertia G ⧸ (I.wildInertia G).subgroupOf (I.inertia G)

/-- The canonical short exact sequence from wild inertia through inertia to tame inertia. -/
@[stacks 09EE, stacks 0BU4 "wild-tame inertia exact sequence"]
noncomputable def tameExtension (I : Ideal R) :
    GroupExtension ((I.wildInertia G).subgroupOf (I.inertia G))
      (I.inertia G) (I.tameInertia G) :=
  { inl := ((I.wildInertia G).subgroupOf (I.inertia G)).subtype
    rightHom := QuotientGroup.mk' ((I.wildInertia G).subgroupOf (I.inertia G))
    inl_injective := Subtype.coe_injective
    range_inl_eq_ker_rightHom := sorry
    rightHom_surjective := QuotientGroup.mk'_surjective _ }

-- Proof strategy: for the Prop field `range_inl_eq_ker_rightHom`, rewrite the range of the
-- subgroup inclusion with `Subgroup.range_subtype` and the quotient kernel with
-- `QuotientGroup.ker_mk'`; both sides are the same subgroup of `I.inertia G`.

/-- The left map in the wild/tame extension is the subgroup inclusion. -/
@[simp, stacks 09EE "wild-tame extension inclusion formula"]
theorem tameExtension_inl_apply (I : Ideal R)
    (sigma : (I.wildInertia G).subgroupOf (I.inertia G)) :
    (I.tameExtension.inl sigma : I.inertia G) = sigma := sorry

-- Proof strategy: unfold `tameExtension`; its left map is explicitly the subgroup subtype, so
-- the statement follows by reflexivity after reducing the structure projection.

/-- The right map in the wild/tame extension is the quotient-class map. -/
@[simp, stacks 09EE "wild-tame extension quotient formula"]
theorem tameExtension_rightHom_apply (I : Ideal R) (sigma : I.inertia G) :
    I.tameExtension.rightHom sigma = QuotientGroup.mk sigma := sorry

-- Proof strategy: unfold `tameExtension`; its right map is explicitly `QuotientGroup.mk'`, whose
-- underlying function is `QuotientGroup.mk`.

/-- The ambient inertia subgroup, viewed inside the decomposition group, is normal.

This is the `subgroupOf` form needed by the conjugation homomorphism; Mathlib's primitive
instance is stated for `I.inertia (MulAction.stabilizer G I)`. -/
@[stacks 0BU5 "inertia is normal in the decomposition group"]
instance inertiaSubgroup_normal (I : Ideal R) :
    ((I.inertia G).subgroupOf (MulAction.stabilizer G I)).Normal := sorry

-- Proof strategy: transport Mathlib's canonical normal instance
-- `I.inertia (MulAction.stabilizer G I).Normal` across `Ideal.coe_mem_inertia` and the equivalence
-- `Subgroup.subgroupOfEquivOfLe (Ideal.inertia_le_stabilizer I)`.

/-- The decomposition quotient is the decomposition group modulo inertia.  It is the canonical
group acting faithfully on the residue extension at the ideal. -/
@[stacks 0BU6 "decomposition group modulo inertia"]
abbrev decompositionQuotient (I : Ideal R) (G : Type v) [Group G]
    [MulSemiringAction G R] :=
  MulAction.stabilizer G I ⧸
    (I.inertia G).subgroupOf (MulAction.stabilizer G I)

/-- The decomposition group of an ideal acts on its inertia group by conjugation.

The construction transports `MulAut.conjNormal` across the canonical equivalence between the
inertia subgroup inside the stabilizer and the ambient inertia subgroup. -/
@[stacks 0BU5 "decomposition-group conjugation on inertia"]
def inertiaConjHom (I : Ideal R) :
    MulAction.stabilizer G I →* MulAut (I.inertia G) :=
  (MulAut.congr
    (Subgroup.subgroupOfEquivOfLe (Ideal.inertia_le_stabilizer I))).toMonoidHom.comp
      (MulAut.conjNormal
        (G := MulAction.stabilizer G I)
        (H := (I.inertia G).subgroupOf (MulAction.stabilizer G I)))

/-- The bundled inertia conjugation homomorphism evaluates as conjugation in the ambient group. -/
@[simp, stacks 0BU5 "inertia conjugation formula"]
theorem inertiaConjHom_apply (I : Ideal R)
    (tau : MulAction.stabilizer G I) (sigma : I.inertia G) :
    (inertiaConjHom I tau sigma : G) = tau * sigma * tau⁻¹ := sorry

-- Proof strategy: unfold `inertiaConjHom`; simplify the transport through
-- `Subgroup.subgroupOfEquivOfLe`, then apply `MulAut.conjNormal_apply` and coerce the resulting
-- equality from the stabilizer subgroup to `G`.

end Ideal
