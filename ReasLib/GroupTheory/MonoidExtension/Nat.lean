module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Quot
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupExtension.Defs
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Monoid extensions by the natural numbers

Explicit homomorphisms describe extensions with left-torsor fibres. The nonnegative
part of a group extension by the integers is such an extension.
-/

@[expose] public section

noncomputable section

universe v w

/-- An inclusion and a degree map form an exact extension with left-torsor fibres when
the inclusion is injective, its range is the degree kernel, the degree map is surjective,
and each pair of equal-degree elements differs by a unique left translation. -/
def NatMonoidExtension.IsExact {G : Type v} {Γ : Type w} [Group G] [Monoid Γ]
    (inl : G →* Γ) (rightHom : Γ →* Multiplicative ℕ) : Prop :=
  Function.Injective inl ∧ MonoidHom.mrange inl = MonoidHom.mker rightHom ∧
    Function.Surjective rightHom ∧
      ∀ γ γ' : Γ, rightHom γ = rightHom γ' → ∃! g : G, γ' = inl g * γ

/-- A monoid extension by the natural numbers is an explicit pair of homomorphisms
satisfying exactness and the left-torsor condition on equal-degree fibres. -/
def NatMonoidExtension (G : Type v) (Γ : Type w) [Group G] [Monoid Γ] :=
  {maps : (G →* Γ) × (Γ →* Multiplicative ℕ) //
    NatMonoidExtension.IsExact maps.1 maps.2}

namespace NatMonoidExtension

variable {G : Type v} {Γ : Type w} [Group G] [Monoid Γ] (S : NatMonoidExtension G Γ)

/-- The inclusion homomorphism of a natural-number monoid extension. -/
abbrev inl : G →* Γ := S.val.1

/-- The degree homomorphism of a natural-number monoid extension. -/
abbrev rightHom : Γ →* Multiplicative ℕ := S.val.2

/-- The inclusion of an extension is injective. -/
abbrev inl_injective : Function.Injective S.inl := S.property.1

/-- The range of an extension's inclusion is the kernel of its degree map. -/
abbrev range_inl_eq_ker_rightHom : MonoidHom.mrange S.inl = MonoidHom.mker S.rightHom :=
  S.property.2.1

/-- The degree map of an extension is surjective. -/
abbrev rightHom_surjective : Function.Surjective S.rightHom := S.property.2.2.1

/-- Equal-degree elements differ by a unique left translation by the kernel group. -/
abbrev eqDegree_leftTorsor :
    ∀ γ γ' : Γ, S.rightHom γ = S.rightHom γ' → ∃! g : G, γ' = S.inl g * γ :=
  S.property.2.2.2

/-- The inclusion lands in the kernel of the degree map. -/
theorem rightHom_inl (g : G) : S.rightHom (S.inl g) = 1 := sorry

/-- The identity has nonnegative degree in a group extension by the integers. -/
theorem nonnegSubmonoid_one_mem {E : Type w} [Group E]
    (T : GroupExtension G E (Multiplicative ℤ)) :
    0 ≤ Multiplicative.toAdd (T.rightHom (1 : E)) := sorry

/-- The product of two elements of nonnegative degree has nonnegative degree. -/
theorem nonnegSubmonoid_mul_mem {E : Type w} [Group E]
    (T : GroupExtension G E (Multiplicative ℤ)) {e f : E}
    (he : 0 ≤ Multiplicative.toAdd (T.rightHom e))
    (hf : 0 ≤ Multiplicative.toAdd (T.rightHom f)) :
    0 ≤ Multiplicative.toAdd (T.rightHom (e * f)) := sorry

/-- The submonoid of elements of nonnegative degree in an integer group extension. -/
def nonnegSubmonoid {E : Type w} [Group E]
    (T : GroupExtension G E (Multiplicative ℤ)) : Submonoid E where
  carrier := {e | 0 ≤ Multiplicative.toAdd (T.rightHom e)}
  one_mem' := nonnegSubmonoid_one_mem T
  mul_mem' := nonnegSubmonoid_mul_mem T

/-- Membership in the nonnegative submonoid is nonnegativity of the integer degree. -/
theorem mem_nonneg_iff {E : Type w} [Group E]
    {T : GroupExtension G E (Multiplicative ℤ)} {e : E} :
    e ∈ nonnegSubmonoid T ↔ 0 ≤ Multiplicative.toAdd (T.rightHom e) := sorry

/-- The monoid of nonnegative elements of an integer group extension. -/
abbrev nonneg {E : Type w} [Group E] (T : GroupExtension G E (Multiplicative ℤ)) :=
  {e : E // e ∈ nonnegSubmonoid T}

/-- Elements included from the kernel group have nonnegative degree. -/
theorem nonnegInl_mem {E : Type w} [Group E]
    (T : GroupExtension G E (Multiplicative ℤ)) (g : G) :
    T.inl g ∈ nonnegSubmonoid T := sorry

/-- The kernel inclusion into the nonnegative monoid preserves the identity. -/
theorem nonnegInl_one {E : Type w} [Group E]
    (T : GroupExtension G E (Multiplicative ℤ)) :
    (⟨T.inl 1, nonnegInl_mem T 1⟩ : nonneg T) = 1 := sorry

/-- The kernel inclusion into the nonnegative monoid preserves multiplication. -/
theorem nonnegInl_mul {E : Type w} [Group E]
    (T : GroupExtension G E (Multiplicative ℤ)) (g h : G) :
    (⟨T.inl (g * h), nonnegInl_mem T (g * h)⟩ : nonneg T) =
      ⟨T.inl g, nonnegInl_mem T g⟩ * ⟨T.inl h, nonnegInl_mem T h⟩ := sorry

/-- The kernel inclusion, with its codomain restricted to elements of nonnegative degree. -/
def nonnegInl {E : Type w} [Group E]
    (T : GroupExtension G E (Multiplicative ℤ)) : G →* nonneg T where
  toFun g := ⟨T.inl g, nonnegInl_mem T g⟩
  map_one' := nonnegInl_one T
  map_mul' := nonnegInl_mul T

/-- The natural-number degree of the identity is zero. -/
theorem nonnegDegree_one {E : Type w} [Group E]
    (T : GroupExtension G E (Multiplicative ℤ)) :
    Multiplicative.ofAdd (Int.toNat (Multiplicative.toAdd (T.rightHom (1 : nonneg T).val))) =
      (1 : Multiplicative ℕ) := sorry

/-- The natural-number degree map preserves multiplication on the nonnegative monoid. -/
theorem nonnegDegree_mul {E : Type w} [Group E]
    (T : GroupExtension G E (Multiplicative ℤ)) (e f : nonneg T) :
    Multiplicative.ofAdd (Int.toNat (Multiplicative.toAdd (T.rightHom (e * f).val))) =
      Multiplicative.ofAdd (Int.toNat (Multiplicative.toAdd (T.rightHom e.val))) *
        Multiplicative.ofAdd (Int.toNat (Multiplicative.toAdd (T.rightHom f.val))) := sorry

/-- The degree map on the nonnegative part, with values in the natural numbers. -/
def nonnegDegree {E : Type w} [Group E]
    (T : GroupExtension G E (Multiplicative ℤ)) : nonneg T →* Multiplicative ℕ where
  toFun e := Multiplicative.ofAdd (Int.toNat (Multiplicative.toAdd (T.rightHom e.val)))
  map_one' := nonnegDegree_one T
  map_mul' := nonnegDegree_mul T

/-- The inclusion and degree maps of the nonnegative part satisfy exactness and the torsor laws. -/
theorem nonnegExtensionLaws {E : Type w} [Group E]
    (T : GroupExtension G E (Multiplicative ℤ)) :
    IsExact (nonnegInl T) (nonnegDegree T) := sorry

/-- The nonnegative part of an integer group extension, as a natural-number monoid extension. -/
def ofGroupExtension {E : Type w} [Group E]
    (T : GroupExtension G E (Multiplicative ℤ)) : NatMonoidExtension G (nonneg T) :=
  ⟨(nonnegInl T, nonnegDegree T), nonnegExtensionLaws T⟩

/-- The nonnegative extension has the restricted inclusion and natural-number degree maps. -/
theorem ofGroupExtension_spec {E : Type w} [Group E]
    (T : GroupExtension G E (Multiplicative ℤ)) :
    (ofGroupExtension T).inl = nonnegInl T ∧
      (ofGroupExtension T).rightHom = nonnegDegree T := sorry

/-- The identity of the kernel group commutes with every element of the extension. -/
theorem centralizer_one_mem (γ : Γ) : S.inl 1 * γ = γ * S.inl 1 := sorry

/-- The product of two kernel elements commuting with an extension element also commutes with it. -/
theorem centralizer_mul_mem (γ : Γ) {g h : G}
    (hg : S.inl g * γ = γ * S.inl g) (hh : S.inl h * γ = γ * S.inl h) :
    S.inl (g * h) * γ = γ * S.inl (g * h) := sorry

/-- The inverse of a kernel element commuting with an extension element also commutes with it. -/
theorem centralizer_inv_mem (γ : Γ) {g : G} (hg : S.inl g * γ = γ * S.inl g) :
    S.inl g⁻¹ * γ = γ * S.inl g⁻¹ := sorry

/-- The subgroup of kernel elements commuting with a specified extension element. -/
def centralizer (γ : Γ) : Subgroup G where
  carrier := {g | S.inl g * γ = γ * S.inl g}
  one_mem' := centralizer_one_mem S γ
  mul_mem' := centralizer_mul_mem S γ
  inv_mem' := centralizer_inv_mem S γ

/-- Centralizer membership means commutation after inclusion into the extension monoid. -/
theorem centralizer_mem_iff {γ : Γ} {g : G} :
    g ∈ S.centralizer γ ↔ S.inl g * γ = γ * S.inl g := sorry

/-- The degree-one fibre of a natural-number monoid extension. -/
def degreeOne : Type w :=
  {γ : Γ // Multiplicative.toAdd (S.rightHom γ) = 1}

/-- A degree-one lift chosen using surjectivity of the degree map. -/
def degreeOneLift : S.degreeOne :=
  ⟨Classical.choose (S.rightHom_surjective (Multiplicative.ofAdd 1)),
    congrArg Multiplicative.toAdd
      (Classical.choose_spec (S.rightHom_surjective (Multiplicative.ofAdd 1)))⟩

/-- The degree of a degree-one element is one. -/
theorem degreeOne_rightHom (γ : S.degreeOne) :
    Multiplicative.toAdd (S.rightHom γ.val) = 1 := sorry

/-- The chosen degree-one lift maps to the natural number one. -/
theorem degreeOneLift_spec : S.rightHom S.degreeOneLift.val = Multiplicative.ofAdd 1 := sorry

/-- Conjugacy of extension elements by elements of the kernel group. -/
def IsGConj (γ γ' : Γ) : Prop :=
  ∃ g : G, S.inl g * γ * S.inl g⁻¹ = γ'

/-- Conjugation by a kernel element preserves degree one. -/
theorem conj_mem_degreeOne (g : G) (γ : S.degreeOne) :
    Multiplicative.toAdd (S.rightHom (S.inl g * γ.val * S.inl g⁻¹)) = 1 := sorry

/-- Conjugation by the identity fixes each degree-one element. -/
theorem conj_one (γ : S.degreeOne) : S.inl 1 * γ.val * S.inl (1 : G)⁻¹ = γ.val := sorry

/-- Conjugation by a product is the composite of conjugation by its factors. -/
theorem conj_mul (g h : G) (γ : S.degreeOne) :
    S.inl (g * h) * γ.val * S.inl (g * h)⁻¹ =
      S.inl g * (S.inl h * γ.val * S.inl h⁻¹) * S.inl g⁻¹ := sorry

/-- The kernel group acts on the degree-one fibre by conjugation. -/
instance instMulAction_degreeOne : MulAction G S.degreeOne where
  smul g γ := ⟨S.inl g * γ.val * S.inl g⁻¹, conj_mem_degreeOne S g γ⟩
  one_smul γ := Subtype.ext (conj_one S γ)
  mul_smul g h γ := Subtype.ext (conj_mul S g h γ)

/-- The conjugation action has its usual formula on underlying extension elements. -/
theorem smul_degreeOne_val (g : G) (γ : S.degreeOne) :
    (g • γ).val = S.inl g * γ.val * S.inl g⁻¹ := sorry

/-- Kernel-group conjugacy on the degree-one fibre is its conjugation orbit relation. -/
theorem IsGConj_iff_orbitRel {γ γ' : S.degreeOne} :
    S.IsGConj γ.val γ'.val ↔ MulAction.orbitRel G S.degreeOne γ γ' := sorry

/-- The kernel-group conjugacy classes of degree-one extension elements. -/
abbrev DegreeOneGConjClass : Type w :=
  MulAction.orbitRel.Quotient G S.degreeOne

/-- Two degree-one orbit classes agree exactly when their representatives are kernel-group conjugate. -/
theorem DegreeOneGConjClass.mk_eq_iff {γ γ' : S.degreeOne} :
    (Quotient.mk (MulAction.orbitRel G S.degreeOne) γ : S.DegreeOneGConjClass) =
        Quotient.mk (MulAction.orbitRel G S.degreeOne) γ' ↔
      S.IsGConj γ.val γ'.val := sorry

/-- The degree-one fibre of an extension of a finite group is finite. -/
instance instFinite_degreeOne [Finite G] : Finite S.degreeOne := sorry

/-- There are finitely many kernel-group conjugacy classes of degree-one elements for a finite kernel. -/
instance instFinite_DegreeOneGConjClass [Finite G] : Finite S.DegreeOneGConjClass := sorry

end NatMonoidExtension
