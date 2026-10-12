/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Quot
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupExtension.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import stacks_project.Chap64.Definition_64_15_2_Trace
public import stacks_project.Chap64.Lemma_64_15_9_Coinvariants

/-!
# Monoid extensions of a finite group by `ℕ`

This leaf owns the exact sequence `1 → G → Γ → ℕ → 1`, the degree-1 fibre, `G`-conjugacy
classes, centralizers `Z_γ`, restriction of scalars along `inl` and subgroups, and the
degree-1 action on coinvariants used by the trivial trace formula.
-/

@[expose] public section

noncomputable section

universe u v w x

open Ring
open scoped MonoidAlgebra Ring

/-- A monoid extension `1 → G → Γ → ℕ → 1` whose equal-degree fibres are left `G`-torsors,
as for the nonnegative part of a group extension `1 → G → E → ℤ → 1`. -/
structure NatMonoidExtension (G : Type v) (Γ : Type w) [Group G] [Monoid Γ] where
  /-- The inclusion homomorphism `G →* Γ`. -/
  inl : G →* Γ
  /-- The projection homomorphism `Γ →* Multiplicative ℕ`. -/
  rightHom : Γ →* Multiplicative ℕ
  /-- The inclusion map is injective. -/
  inl_injective : Function.Injective inl
  /-- Exactness at `Γ`: the image of `inl` is the kernel of `rightHom`. -/
  range_inl_eq_ker_rightHom : MonoidHom.mrange inl = MonoidHom.mker rightHom
  /-- The projection map is surjective. -/
  rightHom_surjective : Function.Surjective rightHom
  /-- Equal-degree fibres are left `G`-torsors: if `rightHom γ = rightHom γ'`, there is a
  unique `g` with `γ' = inl g * γ`. -/
  eqDegree_leftTorsor :
    ∀ γ γ' : Γ, rightHom γ = rightHom γ' → ∃! g : G, γ' = inl g * γ

namespace NatMonoidExtension

variable {G : Type v} {Γ : Type w} [Group G] [Monoid Γ] (S : NatMonoidExtension G Γ)

/-- The inclusion of `G` lands in the kernel of the projection to `ℕ`. -/
theorem rightHom_inl (g : G) : S.rightHom (S.inl g) = 1 :=
  sorry

/-- Equal-degree elements differ by a unique left `G`-translation along `inl`. -/
theorem eqDegree_existsUnique {γ γ' : Γ} (h : S.rightHom γ = S.rightHom γ') :
    ∃! g : G, γ' = S.inl g * γ :=
  sorry

/-- The nonnegative submonoid of a group extension of `Multiplicative ℤ`. -/
def nonnegSubmonoid {E : Type w} [Group E]
    (T : GroupExtension G E (Multiplicative ℤ)) : Submonoid E where
  carrier := {e | 0 ≤ Multiplicative.toAdd (T.rightHom e)}
  one_mem' := sorry
  mul_mem' := sorry

/-- Membership in the nonnegative submonoid is nonnegativity of the image in `ℤ`. -/
theorem mem_nonneg_iff {E : Type w} [Group E]
    {T : GroupExtension G E (Multiplicative ℤ)} {e : E} :
    e ∈ nonnegSubmonoid T ↔ 0 ≤ Multiplicative.toAdd (T.rightHom e) :=
  sorry

/-- The monoid of nonnegative elements of a group extension of `Multiplicative ℤ`. -/
abbrev nonneg {E : Type w} [Group E] (T : GroupExtension G E (Multiplicative ℤ)) :=
  {e : E // e ∈ nonnegSubmonoid T}

/-- The nonnegative part of a group extension `1 → G → E → ℤ → 1`, as a monoid extension
of `G` by `ℕ`. -/
def ofGroupExtension {E : Type w} [Group E]
    (T : GroupExtension G E (Multiplicative ℤ)) :
    NatMonoidExtension G (nonneg T) where
  inl :=
    { toFun := fun g ↦ ⟨T.inl g, sorry⟩
      map_one' := sorry
      map_mul' := sorry }
  rightHom :=
    { toFun := fun e ↦
        Multiplicative.ofAdd (Int.toNat (Multiplicative.toAdd (T.rightHom e.val)))
      map_one' := sorry
      map_mul' := sorry }
  inl_injective := sorry
  range_inl_eq_ker_rightHom := sorry
  rightHom_surjective := sorry
  eqDegree_leftTorsor := sorry

/-- The centralizer `Z_γ = {g ∈ G | gγ = γg}` of `γ` in `G`. -/
def centralizer (γ : Γ) : Subgroup G where
  carrier := {g | S.inl g * γ = γ * S.inl g}
  one_mem' := sorry
  mul_mem' := sorry
  inv_mem' := sorry

/-- Membership in `Z_γ` is commutation with `γ` after inclusion into `Γ`. -/
theorem centralizer_mem_iff {γ : Γ} {g : G} :
    g ∈ S.centralizer γ ↔ S.inl g * γ = γ * S.inl g :=
  sorry

/-- The fibre of `rightHom` over `1 ∈ ℕ`. -/
def degreeOne : Type w :=
  {γ : Γ // Multiplicative.toAdd (S.rightHom γ) = 1}

/-- A chosen degree-1 lift of `1 ∈ ℕ` along `rightHom`. -/
noncomputable def degreeOneLift : S.degreeOne :=
  ⟨Classical.choose (S.rightHom_surjective (Multiplicative.ofAdd 1)), sorry⟩

/-- The defining property of a degree-1 element. -/
theorem degreeOne_rightHom (γ : S.degreeOne) :
    Multiplicative.toAdd (S.rightHom γ.val) = 1 :=
  sorry

/-- `G`-conjugacy on `Γ` along `inl`. -/
def IsGConj (γ γ' : Γ) : Prop :=
  ∃ g : G, S.inl g * γ * S.inl g⁻¹ = γ'

/-- Unfolding of `G`-conjugacy. -/
theorem IsGConj.iff {γ γ' : Γ} :
    S.IsGConj γ γ' ↔ ∃ g : G, S.inl g * γ * S.inl g⁻¹ = γ' :=
  sorry

/-- Conjugation by `G` along `inl` preserves the degree-1 fibre. -/
instance instMulAction_degreeOne : MulAction G S.degreeOne where
  smul g γ := ⟨S.inl g * γ.val * S.inl g⁻¹, sorry⟩
  one_smul := sorry
  mul_smul := sorry

/-- Unfolding of the conjugation action on the degree-1 fibre. -/
theorem smul_degreeOne_val (g : G) (γ : S.degreeOne) :
    (g • γ).val = S.inl g * γ.val * S.inl g⁻¹ :=
  sorry

/-- `G`-conjugacy on degree-1 elements is the conjugation orbit relation. -/
theorem IsGConj_iff_orbitRel {γ γ' : S.degreeOne} :
    S.IsGConj γ.val γ'.val ↔ MulAction.orbitRel G S.degreeOne γ γ' :=
  sorry

/-- `G`-conjugacy classes of degree-1 elements of `Γ`. -/
abbrev DegreeOneGConjClass : Type w :=
  MulAction.orbitRel.Quotient G S.degreeOne

/-- Classes agree iff the representatives are `G`-conjugate. -/
theorem DegreeOneGConjClass.mk_eq_iff {γ γ' : S.degreeOne} :
    (Quotient.mk (MulAction.orbitRel G S.degreeOne) γ : S.DegreeOneGConjClass) =
        Quotient.mk (MulAction.orbitRel G S.degreeOne) γ' ↔
      S.IsGConj γ.val γ'.val :=
  sorry

/-- The degree-1 fibre is finite: the left `G`-torsor property identifies it with `G`. -/
instance instFinite_degreeOne [Finite G] : Finite S.degreeOne :=
  sorry

/-- There are finitely many `G`-conjugacy classes of degree-1 elements. -/
instance instFinite_DegreeOneGConjClass [Finite G] : Finite S.DegreeOneGConjClass :=
  sorry

end NatMonoidExtension

namespace MonoidAlgebra

/-- The given `Λ[G]`-action on `P` is restriction of the `Λ[Γ]`-action along `S.inl`. -/
class IsRestrictionAlongInl (Λ : Type u) {G : Type v} {Γ : Type w}
    [Ring Λ] [Group G] [Monoid Γ]
    (S : NatMonoidExtension G Γ) (P : Type x)
    [AddCommGroup P] [Module (Λ[Γ]) P] [Module (Λ[G]) P] : Prop where
  /-- Scalar multiplication by `Λ[G]` agrees with the pushed-forward `Λ[Γ]`-action. -/
  smul_eq : ∀ (x : Λ[G]) (p : P), x • p = mapDomainRingHom Λ S.inl x • p

/-- Package agreement of the `Λ[G]`-action with restriction along `S.inl`. -/
theorem IsRestrictionAlongInl.of_smul_eq
    {Λ : Type u} {G : Type v} {Γ : Type w} {P : Type x}
    [Ring Λ] [Group G] [Monoid Γ]
    [AddCommGroup P] [Module (Λ[Γ]) P] [Module (Λ[G]) P]
    (S : NatMonoidExtension G Γ)
    (h : ∀ (x : Λ[G]) (p : P), x • p = mapDomainRingHom Λ S.inl x • p) :
    IsRestrictionAlongInl Λ S P :=
  sorry

/-- Unfolding of the restriction identity. -/
theorem IsRestrictionAlongInl.smul_eq_iff
    {Λ : Type u} {G : Type v} {Γ : Type w} {P : Type x}
    [Ring Λ] [Group G] [Monoid Γ]
    [AddCommGroup P] [Module (Λ[Γ]) P] [Module (Λ[G]) P]
    (S : NatMonoidExtension G Γ) [IsRestrictionAlongInl Λ S P] :
    ∀ (x : Λ[G]) (p : P), x • p = mapDomainRingHom Λ S.inl x • p :=
  sorry

/-- On group basis elements, restriction along `inl` agrees with the `Λ[Γ]`-action. -/
theorem IsRestrictionAlongInl.smul_single
    {Λ : Type u} {G : Type v} {Γ : Type w} {P : Type x}
    [Ring Λ] [Group G] [Monoid Γ]
    [AddCommGroup P] [Module (Λ[Γ]) P] [Module (Λ[G]) P]
    (S : NatMonoidExtension G Γ) [IsRestrictionAlongInl Λ S P] (g : G) (p : P) :
    (single g (1 : Λ) : Λ[G]) • p = (single (S.inl g) (1 : Λ) : Λ[Γ]) • p :=
  sorry

variable {Λ : Type u} {G : Type v} {Γ : Type w} {P : Type x}
variable [Ring Λ] [Group G] [Monoid Γ]
variable [AddCommGroup P] [Module (Λ[Γ]) P]
variable (S : NatMonoidExtension G Γ)

/-- Restriction of scalars along `mapDomainRingHom Λ S.inl : Λ[G] →+* Λ[Γ]`. This cannot
be a typeclass instance: `S` is not determined by `Module (Λ[G]) P`. -/
@[reducible] def moduleRestrictInl : Module (Λ[G]) P :=
  Module.compHom P (mapDomainRingHom Λ S.inl)

variable [Module (Λ[G]) P]

/-- Restriction of scalars from `Λ[G]` to a subgroup algebra `Λ[H]`. -/
instance moduleRestrictSubgroup (H : Subgroup G) : Module (Λ[H]) P :=
  Module.compHom P (mapDomainRingHom Λ H.subtype)

/-- Finite generation over `Λ[G]` restricts to a finite subgroup algebra. -/
instance finiteRestrictSubgroup (H : Subgroup G) [Finite G]
    [Module.Finite (Λ[G]) P] : Module.Finite (Λ[H]) P :=
  sorry

/-- Projectivity over `Λ[G]` restricts to a finite subgroup algebra. -/
instance projectiveRestrictSubgroup (H : Subgroup G) [Finite G]
    [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P] :
    Module.Projective (Λ[H]) P :=
  sorry

end MonoidAlgebra

namespace LinearMap.FiniteProjective

variable {Λ : Type u} {G : Type v} {Γ : Type w} {P : Type x}
variable [Ring Λ] [Group G] [Monoid Γ]
variable [AddCommGroup P] [Module (Λ[Γ]) P] [Module Λ P]

/-- The `Λ`-linear action of an element of `Γ` on a left `Λ[Γ]`-module. -/
def smulEnd [IsScalarTower Λ (Λ[Γ]) P] (γ : Γ) : Module.End Λ P where
  toFun p := (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p
  map_add' := sorry
  map_smul' := sorry

/-- Unfolding of the `Λ`-linear action of `γ`. -/
theorem smulEnd_apply [IsScalarTower Λ (Λ[Γ]) P] (γ : Γ) (p : P) :
    (smulEnd γ : Module.End Λ P) p = (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p :=
  sorry

variable [Module (Λ[G]) P]
variable (S : NatMonoidExtension G Γ)

/-- The `Λ[Z_γ]`-linear action of `γ` on `P`. -/
def smulEndZ [MonoidAlgebra.IsRestrictionAlongInl Λ S P] (γ : Γ) :
    Module.End (Λ[S.centralizer γ]) P where
  toFun p := (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p
  map_add' := sorry
  map_smul' := sorry

/-- Unfolding of the `Λ[Z_γ]`-linear action of `γ`. -/
theorem smulEndZ_apply [MonoidAlgebra.IsRestrictionAlongInl Λ S P] (γ : Γ) (p : P) :
    (smulEndZ S γ : Module.End (Λ[S.centralizer γ]) P) p =
      (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p :=
  sorry

end LinearMap.FiniteProjective

namespace LinearMap.FiniteProjective

variable {Λ : Type u} {G : Type v} {Γ : Type w}
variable [Ring Λ] [Group G] [Monoid Γ] [Finite G]
variable (S : NatMonoidExtension G Γ) (P : Type x)
variable [AddCommGroup P] [Module (Λ[Γ]) P] [Module (Λ[G]) P] [Module Λ P]
variable [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P]

/-- `G`-conjugate degree-1 elements have equal `Z_γ`-traces. -/
theorem gConj_traceG_eq
    [IsScalarTower Λ (Λ[G]) P] [IsScalarTower Λ (Λ[Γ]) P]
    [MonoidAlgebra.IsRestrictionAlongInl Λ S P]
    {γ γ' : S.degreeOne}
    (h : MulAction.orbitRel G S.degreeOne γ γ') :
    traceG (smulEndZ S γ.val : Module.End (Λ[S.centralizer γ.val]) P) =
      traceG (smulEndZ S γ'.val : Module.End (Λ[S.centralizer γ'.val]) P) :=
  sorry

/-- The well-defined `Z_γ`-trace of a `G`-conjugacy class of degree-1 elements. -/
noncomputable def conjClassTrace
    [IsScalarTower Λ (Λ[G]) P] [IsScalarTower Λ (Λ[Γ]) P]
    [MonoidAlgebra.IsRestrictionAlongInl Λ S P] :
    S.DegreeOneGConjClass → Λ♮ :=
  Quotient.lift
    (fun γ : S.degreeOne ↦
      traceG (smulEndZ S γ.val : Module.End (Λ[S.centralizer γ.val]) P))
    (fun _ _ h ↦ gConj_traceG_eq S P h)

/-- The class trace on a representative is the `Z_γ`-trace of that element. -/
theorem conjClassTrace_mk
    [IsScalarTower Λ (Λ[G]) P] [IsScalarTower Λ (Λ[Γ]) P]
    [MonoidAlgebra.IsRestrictionAlongInl Λ S P] (γ : S.degreeOne) :
    conjClassTrace S P (Quotient.mk (MulAction.orbitRel G S.degreeOne) γ) =
      traceG (smulEndZ S γ.val : Module.End (Λ[S.centralizer γ.val]) P) :=
  sorry

end LinearMap.FiniteProjective
