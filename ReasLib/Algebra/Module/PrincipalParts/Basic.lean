module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.GroupTheory.GroupAction.Ring
public import ReasLib.Algebra.Module.DifferentialOperator.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal Parts of a Module

This file owns the principal-parts module and its representation of bounded
order differential operators.

@stack 09CK
@stack 09CL
-/

public section

universe u

noncomputable section

namespace PrincipalParts

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- The free `S`-module on the underlying set of `M` used to present principal parts. -/
private abbrev free : Type u := M →₀ S

/-- The basis vector `[m]` in the free module used to present principal parts. -/
private abbrev basisVector (m : M) : M →₀ S :=
  Finsupp.single m (1 : S)

/-- The iterated commutator relation attached to a finite list of scalars in `S`. -/
private def commutatorRelation : List S → M → M →₀ S
  | [], m => basisVector m
  | s :: l, m =>
      commutatorRelation l (s • m) -
        s • commutatorRelation l m

/-- Recursively evaluate the iterated scalar commutator determined by a
finite list of scalars. -/
private def iteratedCommutatorEval
    (N : Type u) [AddCommGroup N] [Module S N] (l : List S) (f : M → N) : M → N :=
  match l with
  | [] => f
  | s :: l =>
      fun m ↦
        iteratedCommutatorEval N l f (s • m) - s • iteratedCommutatorEval N l f m

/-- The generating relations for the `k`-th module of principal parts of `M` over `R → S`. -/
private def relationSet
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] (k : ℕ) :
    Set (M →₀ S) :=
  { x |
      (∃ m m' : M,
        x = basisVector (m + m') -
          basisVector m -
          basisVector m') ∨
        (∃ r : R, ∃ m : M,
          x = (algebraMap R S r) • basisVector m -
            basisVector (r • m)) ∨
          ∃ l : List S, l.length = k + 1 ∧ ∃ m : M,
            x = commutatorRelation l m }

/-- The submodule of relations used to define the `k`-th module of principal parts. -/
def relationSubmodule
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] (k : ℕ) :
    Submodule S (M →₀ S) :=
  Submodule.span S (relationSet R S M k)

/-- The `k`-th module of principal parts of `M` over `R → S`, presented by generators and
relations. -/
@[stacks 09CL]
abbrev module
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] (k : ℕ) :
    Type u :=
  (M →₀ S) ⧸ (relationSubmodule R S M k : Submodule S (M →₀ S))

/-- Additivity of the universal class map `M → PrincipalParts.module R S M k`. -/
private theorem universalDifferential_map_add (k : ℕ) :
    ∀ m m' : M,
      (relationSubmodule R S M k).mkQ
          (basisVector (m + m')) =
        (relationSubmodule R S M k).mkQ
            (basisVector m) +
          (relationSubmodule R S M k).mkQ
            (basisVector m') := by
  intro m m'
  apply (Submodule.Quotient.eq (relationSubmodule R S M k)).2
  have hrel :
      basisVector (m + m') - basisVector m - basisVector m' ∈
        relationSubmodule R S M k :=
    Submodule.subset_span <| Or.inl ⟨m, m', rfl⟩
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hrel

/-- Compatibility of the universal class map `M → PrincipalParts.module R S M k` with the
`R`-action. -/
private theorem universalDifferential_map_smul (k : ℕ) :
    ∀ (r : R) (m : M),
      (relationSubmodule R S M k).mkQ
          (basisVector (r • m)) =
        r • (relationSubmodule R S M k).mkQ
          (basisVector m) := by
  intro r m
  apply (Submodule.Quotient.eq (relationSubmodule R S M k)).2
  have hrel :
      (algebraMap R S r) • basisVector m - basisVector (r • m) ∈
        relationSubmodule R S M k :=
    Submodule.subset_span <| Or.inr <| Or.inl ⟨r, m, rfl⟩
  simpa [Algebra.smul_def, sub_eq_add_neg, add_comm] using
    (relationSubmodule R S M k).neg_mem hrel

/-- The universal `R`-linear map `M → PrincipalParts.module R S M k` sending `m` to the class
of `[m]`. -/
@[stacks 09CK "universal principal-parts differential"]
def universalDifferential (k : ℕ) :
    M →ₗ[R] PrincipalParts.module R S M k where
  toFun m := (relationSubmodule R S M k).mkQ (basisVector m)
  map_add' := universalDifferential_map_add k
  map_smul' := universalDifferential_map_smul k

/-- Order-`k` differential operators encoded on the free presentation of principal parts. -/
private def presentedOperatorsSubmodule
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] :
    Submodule S ((M →₀ S) →ₗ[S] N) :=
  LinearMap.ker <| LinearMap.lcomp S N (relationSubmodule R S M k).subtype

/-- Precomposition with the quotient map `free → PrincipalParts.module R S M k`. -/
private abbrev precompose
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] :
    (module R S M k →ₗ[S] N) →ₗ[S] ((M →₀ S) →ₗ[S] N) :=
  LinearMap.lcomp S N (relationSubmodule R S M k).mkQ

-- Proof sketch: the quotient map from `free` to `module k` is
-- universal among `S`-linear maps annihilating `relationSubmodule k`.
/-- The image of precomposition with the quotient map is the presentation-level differential
operator submodule. -/
private theorem precompose_range_eq_submodule
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] :
    LinearMap.range (precompose R S M k N) =
      presentedOperatorsSubmodule R S M k N := by
  let p := relationSubmodule R S M k
  ext F
  constructor
  · rintro ⟨L, rfl⟩
    -- A map factoring through the quotient vanishes on the relation submodule by construction.
    rw [presentedOperatorsSubmodule, LinearMap.mem_ker]
    ext x
    have hx : p.mkQ x = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact x.2
    change L (p.mkQ x) = 0
    rw [hx]
    simp
  · intro hF
    rw [presentedOperatorsSubmodule, LinearMap.mem_ker] at hF
    -- Conversely, any map killing the relations descends uniquely to the quotient.
    have hker : p ≤ LinearMap.ker F := by
      intro x hx
      have hzero := LinearMap.congr_fun hF ⟨x, hx⟩
      simpa [LinearMap.lcomp_apply] using hzero
    refine ⟨p.liftQ F hker, ?_⟩
    ext x
    simp [precompose]

/-- A presentation-level differential operator vanishes on every
defining principal-parts relation. -/
private theorem presented_apply_eq_zero_of_mem_relation
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N]
    (D : presentedOperatorsSubmodule R S M k N)
    {x : M →₀ S}
    (hx : x ∈ relationSubmodule R S M k) :
    D.1 x = 0 := by
  let p := relationSubmodule R S M k
  have hker : LinearMap.lcomp S N p.subtype D.1 = 0 := by
    simpa [presentedOperatorsSubmodule, LinearMap.mem_ker] using D.2
  -- Membership in the kernel says exactly that `D` kills every element of the relation submodule.
  have hzero := LinearMap.congr_fun hker ⟨x, hx⟩
  change D.1 x = 0 at hzero
  exact hzero

/-- Evaluating a commutator relation under any `S`-linear map on the
free presentation recovers the corresponding iterated scalar commutator on basis evaluation. -/
private theorem commutatorRelation_apply
    (N : Type u) [AddCommGroup N] [Module S N]
    (L : (M →₀ S) →ₗ[S] N) :
    ∀ l : List S, ∀ m : M,
      L (commutatorRelation l m) =
        iteratedCommutatorEval N l (fun m ↦ L (basisVector m)) m := by
  intro l
  induction l with
  | nil =>
      intro m
      -- The empty commutator relation is just the basis vector `[m]`.
      rfl
  | cons s l ih =>
      intro m
      -- The recursive relation matches the recursive commutator evaluation after linearity.
      rw [commutatorRelation, LinearMap.map_sub, LinearMap.map_smul, ih, ih]
      rfl

/-- The list recursion for iterated commutators agrees with taking one
scalar commutator first and then iterating on the tail. -/
private theorem iteratedCommutatorEval_cons_scalarCommutator
    (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (E : M →ₗ[R] N) (g : S) (l : List S) (m : M) :
    iteratedCommutatorEval N (g :: l) (fun m ↦ E m) m =
      iteratedCommutatorEval N l (fun m ↦ E.scalarCommutator g m) m := by
  induction l generalizing m with
  | nil =>
      -- For an empty tail, the statement is exactly the scalar-commutator formula.
      simp [iteratedCommutatorEval]
  | cons s l ih =>
      -- After one more recursive step, both sides are obtained from the induction hypothesis by
      -- expanding the outer commutators and commuting the scalar actions in the commutative ring.
      calc
        iteratedCommutatorEval N (g :: s :: l) (fun m ↦ E m) m =
            iteratedCommutatorEval N (g :: l) (fun m ↦ E m) (s • m) -
              s • iteratedCommutatorEval N (g :: l) (fun m ↦ E m) m := by
          simp [iteratedCommutatorEval, smul_smul, sub_eq_add_neg, add_assoc, add_left_comm,
            add_comm, mul_comm]
        _ =
            iteratedCommutatorEval N l (fun m ↦ E.scalarCommutator g m) (s • m) -
              s • iteratedCommutatorEval N l (fun m ↦ E.scalarCommutator g m) m := by
          rw [ih, ih]
        _ = iteratedCommutatorEval N (s :: l) (fun m ↦ E.scalarCommutator g m) m := by
          rfl

/-- Order-`k` differential operators are exactly the maps whose
length-`k + 1` iterated scalar commutators vanish. -/
private theorem isDifferentialOperatorOfOrder_iff_iteratedCommutatorEval_eq_zero
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (E : M →ₗ[R] N) :
    E.IsDifferentialOperatorOfOrder S k ↔
      ∀ l : List S, l.length = k + 1 → ∀ m : M,
        iteratedCommutatorEval N l (fun m ↦ E m) m = 0 := by
  induction k generalizing E with
  | zero =>
      constructor
      · intro h l hl m
        rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff] at h
        cases l with
        | nil =>
            simp at hl
        | cons g l =>
            cases l with
            | nil =>
                -- For a singleton list, the iterated commutator is the ordinary scalar commutator.
                simpa [iteratedCommutatorEval, LinearMap.scalarCommutator_apply] using
                  sub_eq_zero.mpr (h g m)
            | cons g' l =>
                simp at hl
      · intro h
        rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
        intro g m
        -- The converse reads the vanishing condition on the singleton list `[g]`.
        have hzero := h [g] (by simp) m
        exact sub_eq_zero.mp <| by
          simpa [iteratedCommutatorEval, LinearMap.scalarCommutator_apply] using hzero
  | succ k ih =>
      constructor
      · intro h l hl m
        rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff] at h
        cases l with
        | nil =>
            simp at hl
        | cons g l =>
            have hl' : l.length = k + 1 := by
              simpa using hl
            -- Peel off the first scalar and apply the induction hypothesis to the scalar
            -- commutator.
            have hzero :=
              (ih (E := E.scalarCommutator g)).1 (h g) l hl' m
            simpa [iteratedCommutatorEval_cons_scalarCommutator] using hzero
      · intro h
        rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff]
        intro g
        -- Vanishing on lists of length `k + 2` specializes to vanishing of the scalar commutator
        -- on tails of length `k + 1`.
        exact (ih (E := E.scalarCommutator g)).2 (by
          intro l hl m
          have hzero := h (g :: l) (by simpa using congrArg Nat.succ hl) m
          simpa [iteratedCommutatorEval_cons_scalarCommutator] using hzero)

/-- The quotient presentation identifies maps out of `PrincipalParts.module R S M k` with
presentation-level differential operators. -/
private noncomputable def representingEquivPresented
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] :
    (module R S M k →ₗ[S] N) ≃ₗ[S]
      presentedOperatorsSubmodule R S M k N :=
  let p := relationSubmodule R S M k
  let e₁ :
      (module R S M k →ₗ[S] N) ≃ₗ[S]
        LinearMap.range (precompose R S M k N) :=
    LinearEquiv.ofInjective
      (precompose R S M k N)
      (LinearMap.lcomp_injective_of_surjective p.mkQ (Submodule.mkQ_surjective p))
  let e₂ :
      LinearMap.range (precompose R S M k N) ≃ₗ[S]
        presentedOperatorsSubmodule R S M k N :=
    LinearEquiv.ofEq
      (LinearMap.range (precompose R S M k N))
      (presentedOperatorsSubmodule R S M k N)
      (precompose_range_eq_submodule k N)
  e₁.trans e₂

-- Proof sketch: evaluate a presentation-level operator on basis vectors `[m]`; the additivity and
-- `R`-linearity relations make the resulting map `M → N` `R`-linear.
/-- Evaluating a presentation-level operator on basis vectors is
additive in `M`. -/
private theorem operatorEvalAdd
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : presentedOperatorsSubmodule R S M k N) :
    ∀ m m' : M,
      D.1 (basisVector (m + m')) =
        D.1 (basisVector m) +
          D.1 (basisVector m') := by
  intro m m'
  let p := relationSubmodule R S M k
  have hrel :
      basisVector (m + m') -
          basisVector m -
          basisVector m' ∈ p := by
    apply Submodule.subset_span
    exact Or.inl ⟨m, m', rfl⟩
  -- Applying `D` to the additive generator gives the additivity constraint on basis vectors.
  have hzero :=
    presented_apply_eq_zero_of_mem_relation k N D hrel
  rw [LinearMap.map_sub, LinearMap.map_sub] at hzero
  have hzero' :
      D.1 (basisVector (m + m')) -
          (D.1 (basisVector m) +
            D.1 (basisVector m')) = 0 := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hzero
  exact sub_eq_zero.mp hzero'

/-- Evaluating a presentation-level operator on basis vectors is
compatible with the `R`-action on `M`. -/
private theorem operatorEvalSmul
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : presentedOperatorsSubmodule R S M k N) :
    ∀ (r : R) (m : M),
      D.1 (basisVector (r • m)) =
        r • D.1 (basisVector m) := by
  intro r m
  let p := relationSubmodule R S M k
  have hrel :
      (algebraMap R S r) • basisVector m -
          basisVector (r • m) ∈ p := by
    apply Submodule.subset_span
    exact Or.inr <| Or.inl ⟨r, m, rfl⟩
  -- Applying `D` to the scalar relation identifies evaluation on `[r • m]` with scalar action.
  have hzero :=
    presented_apply_eq_zero_of_mem_relation k N D hrel
  rw [LinearMap.map_sub, LinearMap.map_smul] at hzero
  have hzero' :
      (algebraMap R S r) • D.1 (basisVector m) -
          D.1 (basisVector (r • m)) = 0 := by
    simpa using hzero
  have hEq :
      D.1 (basisVector (r • m)) =
        (algebraMap R S r) • D.1 (basisVector m) :=
    (sub_eq_zero.mp hzero').symm
  simpa [Algebra.smul_def] using hEq

/-- Evaluating a presentation-level operator on basis vectors produces
an `R`-linear map on `M`. -/
private def operatorToLinearMapFun
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : presentedOperatorsSubmodule R S M k N) :
    M →ₗ[R] N where
  toFun m := D.1 (basisVector m)
  map_add' := operatorEvalAdd k N D
  map_smul' := operatorEvalSmul k N D

/-- The basis-evaluation construction is additive in the presented
operator. -/
private theorem operatorToLinearMapFun_add
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    ∀ D E : presentedOperatorsSubmodule R S M k N,
      operatorToLinearMapFun k N (D + E) =
        operatorToLinearMapFun k N D +
          operatorToLinearMapFun k N E := by
  intro D E
  -- Addition is pointwise on the underlying presentation-level maps.
  ext m
  rfl

/-- The basis-evaluation construction is `S`-linear in the presented
operator. -/
private theorem operatorToLinearMapFun_smul
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    ∀ (s : S) (D : presentedOperatorsSubmodule R S M k N),
      operatorToLinearMapFun k N (s • D) =
        s • operatorToLinearMapFun k N D := by
  intro s D
  -- Scalar multiplication is also pointwise on the free-presentation encoding.
  ext m
  rfl

/-- Forget the free-presentation encoding of a differential operator by evaluating on basis
vectors. -/
private def operatorToLinearMap (k : ℕ) (N : Type u)
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    presentedOperatorsSubmodule R S M k N →ₗ[S] (M →ₗ[R] N) where
  toFun := operatorToLinearMapFun k N
  map_add' := operatorToLinearMapFun_add k N
  map_smul' := operatorToLinearMapFun_smul k N

-- Proof sketch: the defining presentation relations were chosen so that annihilating them is
-- equivalent to satisfying the recursive commutator definition from `Definition 10.133.1`.
/-- A presentation-level differential operator determines an ordinary differential operator. -/
private theorem operatorToDifferentialOperator_mem
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : presentedOperatorsSubmodule R S M k N) :
    operatorToLinearMap k N D ∈
      differentialOperatorsOrderLESubmodule R S M k N := by
  -- Route correction: prove the recursive differential-operator condition through the explicit
  -- iterated commutator presentation, rather than by a bespoke induction inside this membership
  -- proof.
  change (operatorToLinearMap k N D).IsDifferentialOperatorOfOrder S k
  refine
    (isDifferentialOperatorOfOrder_iff_iteratedCommutatorEval_eq_zero
      (k := k) (N := N) (E := operatorToLinearMap k N D)).2 ?_
  intro l hl m
  let p := relationSubmodule R S M k
  have hrel : commutatorRelation l m ∈ p := by
    apply Submodule.subset_span
    exact Or.inr <| Or.inr ⟨l, hl, m, rfl⟩
  -- The length-`k + 1` commutator generator lies in the presentation kernel, so `D` kills it.
  have hzero :=
    presented_apply_eq_zero_of_mem_relation k N D hrel
  rw [commutatorRelation_apply (N := N) D.1 l m] at hzero
  simpa [operatorToLinearMap,
      operatorToLinearMapFun] using hzero

/-- The map from presentation-level differential operators to ordinary differential operators. -/
private def operatorToDifferentialOperator (k : ℕ) (N : Type u)
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    presentedOperatorsSubmodule R S M k N →ₗ[S]
      differentialOperatorsOrderLE R S M k N :=
  LinearMap.codRestrict
    (differentialOperatorsOrderLESubmodule R S M k N)
    (operatorToLinearMap k N)
    (operatorToDifferentialOperator_mem k N)

-- Proof sketch: extend an ordinary differential operator `D : M → N` `S`-linearly from the basis
-- vectors `[m]`, and use the differential-operator condition to show that the defining relations of
-- `module` vanish.
/-- The free extension attached to a differential operator. -/
private def differentialOperatorOnFreeFun
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : differentialOperatorsOrderLE R S M k N) :
    (M →₀ S) →ₗ[S] N :=
  Finsupp.linearCombination S fun m ↦ (D : M →ₗ[R] N) m

/-- The free-extension construction is additive in the differential
operator. -/
private theorem differentialOperatorOnFreeFun_add
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    ∀ D E : differentialOperatorsOrderLE R S M k N,
      differentialOperatorOnFreeFun k N (D + E) =
        differentialOperatorOnFreeFun k N D +
          differentialOperatorOnFreeFun k N E := by
  intro D E
  -- It is enough to compare the two `S`-linear maps on basis vectors of the free module.
  apply Finsupp.lhom_ext
  intro m s
  simp [differentialOperatorOnFreeFun]

/-- The free-extension construction is `S`-linear in the differential
operator. -/
private theorem differentialOperatorOnFreeFun_smul
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    ∀ (s : S) (D : differentialOperatorsOrderLE R S M k N),
      differentialOperatorOnFreeFun k N (s • D) =
        s • differentialOperatorOnFreeFun k N D := by
  intro s D
  -- The free extension respects the external `S`-action pointwise on basis vectors.
  apply Finsupp.lhom_ext
  intro m t
  simp [differentialOperatorOnFreeFun]
  simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc]

/-- Encode an ordinary differential operator as an `S`-linear map on the free presentation. -/
private def differentialOperatorOnFree
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    differentialOperatorsOrderLE R S M k N →ₗ[S] ((M →₀ S) →ₗ[S] N) where
  toFun := differentialOperatorOnFreeFun k N
  map_add' := differentialOperatorOnFreeFun_add k N
  map_smul' := differentialOperatorOnFreeFun_smul k N

/-- The free extension of a differential operator evaluates a basis
vector `[m]` to the original value `D m`. -/
private theorem differentialOperatorOnFree_basisVector
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : differentialOperatorsOrderLE R S M k N) (m : M) :
    differentialOperatorOnFree k N D
        (basisVector m) =
      (D : M →ₗ[R] N) m := by
  -- The free extension is determined by its values on basis vectors.
  simp [differentialOperatorOnFree,
    differentialOperatorOnFreeFun,
    basisVector, Finsupp.linearCombination_single]

/-- The free extension sends a single basis vector with coefficient
`s` to `s • D m`. -/
private theorem differentialOperatorOnFree_single
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : differentialOperatorsOrderLE R S M k N) (m : M) (s : S) :
    differentialOperatorOnFree k N D (Finsupp.single m s) =
      s • (D : M →ₗ[R] N) m := by
  -- The free extension is the linear combination map, so it reads the coefficient of `[m]`.
  simp [differentialOperatorOnFree,
    differentialOperatorOnFreeFun,
    Finsupp.linearCombination_single]

-- Proof sketch: the ordinary differential-operator identities imply that the additive,
-- `R`-linear, and commutator generators of `relationSubmodule k` are sent to `0`.
/-- An ordinary differential operator yields a presentation-level operator annihilating the
principal-parts relations. -/
private theorem differentialOperatorOnFree_memPresented
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : differentialOperatorsOrderLE R S M k N) :
    differentialOperatorOnFree k N D ∈
      presentedOperatorsSubmodule R S M k N := by
  rw [presentedOperatorsSubmodule, LinearMap.mem_ker]
  ext x
  let F := differentialOperatorOnFree k N D
  change F x.1 = 0
  -- It suffices to check vanishing on the spanning generators of the relation submodule.
  exact Submodule.span_induction (p := fun y _ ↦ F y = 0)
    (by
    intro y hy
    rcases hy with hadd | hsmul | hcomm
    · rcases hadd with ⟨m, m', rfl⟩
      -- The additive generator records additivity of the underlying `R`-linear map.
      rw [LinearMap.map_sub, LinearMap.map_sub]
      rw [differentialOperatorOnFree_basisVector,
        differentialOperatorOnFree_basisVector,
        differentialOperatorOnFree_basisVector]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        sub_eq_zero.mpr ((D : M →ₗ[R] N).map_add m m')
    · rcases hsmul with ⟨r, m, rfl⟩
      -- The `R`-linear generator records compatibility with the `R`-action.
      have hEq :
          (algebraMap R S r) • (D : M →ₗ[R] N) m =
            (D : M →ₗ[R] N) (r • m) := by
        simpa [Algebra.smul_def] using ((D : M →ₗ[R] N).map_smul r m).symm
      rw [LinearMap.map_sub, LinearMap.map_smul]
      rw [differentialOperatorOnFree_basisVector,
        differentialOperatorOnFree_basisVector]
      simpa using sub_eq_zero.mpr hEq
    · rcases hcomm with ⟨l, hl, m, rfl⟩
      -- The length-`k + 1` commutator generators vanish by the differential-operator
      -- hypothesis and the commutator evaluation lemma.
      have hzero :=
        (isDifferentialOperatorOfOrder_iff_iteratedCommutatorEval_eq_zero
          (k := k) (N := N) (E := (D : M →ₗ[R] N))).1 D.2 l hl m
      have hEval :=
        commutatorRelation_apply
          (N := N) (differentialOperatorOnFree k N D) l m
      rw [hEval]
      simpa [differentialOperatorOnFree_basisVector] using
        hzero)
    (by
      -- The free extension is linear, so it sends `0` to `0`.
      simp)
    (by
      intro a b _ _ ha hb
      -- Vanishing is preserved under addition because the free extension is linear.
      simpa [map_add, ha, hb])
    (by
      intro s y _ hy
      -- Vanishing is also preserved under scalar multiplication.
      simpa [map_smul, hy])
    x.2

/-- The map from ordinary differential operators to the presentation-level encoding. -/
private def differentialOperatorToPresentedOperator
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    differentialOperatorsOrderLE R S M k N →ₗ[S]
      presentedOperatorsSubmodule R S M k N :=
  LinearMap.codRestrict
    (presentedOperatorsSubmodule R S M k N)
    (differentialOperatorOnFree k N)
    (differentialOperatorOnFree_memPresented k N)

-- Proof sketch: the two constructions above are inverse by construction on basis vectors `[m]`,
-- and by the universal property of the free module they are inverse on the whole presentation.
/-- The free-presentation encoding of differential operators is equivalent to the canonical owner
submodule of ordinary differential operators. -/
private noncomputable def presentedOperatorsEquiv
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    presentedOperatorsSubmodule R S M k N ≃ₗ[S]
      differentialOperatorsOrderLE R S M k N :=
  LinearEquiv.ofLinear
    (operatorToDifferentialOperator k N)
    (differentialOperatorToPresentedOperator k N)
    (by
      -- On ordinary differential operators, extend from basis vectors and then evaluate back.
      ext D m
      simp [operatorToDifferentialOperator,
        operatorToLinearMap,
        operatorToLinearMapFun,
        differentialOperatorToPresentedOperator,
        differentialOperatorOnFree_basisVector])
    (by
      -- On presented operators, equality on basis vectors determines equality on the free module.
      apply LinearMap.ext
      intro D
      apply Subtype.ext
      apply Finsupp.lhom_ext
      intro m s
      -- Compare both sides on the generator `single m s`.
      calc
        ((differentialOperatorToPresentedOperator k N
              (operatorToDifferentialOperator k N D) :
            (M →₀ S) →ₗ[S] N) (Finsupp.single m s)) =
            s • ((operatorToDifferentialOperator k N D : M →ₗ[R] N) m) := by
          simpa [differentialOperatorToPresentedOperator] using
            differentialOperatorOnFree_single k N
              (operatorToDifferentialOperator k N D) m s
        _ = s • D.1 (basisVector m) := by
          rfl
        _ = D.1 (Finsupp.single m s) := by
          have hsingle : (Finsupp.single m s : M →₀ S) = s • basisVector m := by
            ext a
            by_cases h : a = m
            · subst h
              simp [basisVector]
            · simp [basisVector, h]
          rw [hsingle, LinearMap.map_smul]
      )

/-- `PrincipalParts.module R S M k` represents order-`k` differential operators
from `M` to an `S`-module `N`. -/
@[stacks 09CK]
noncomputable def representingEquiv
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (k : ℕ) (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    (PrincipalParts.module R S M k →ₗ[S] N) ≃ₗ[S]
      differentialOperatorsOrderLE R S M k N :=
  (representingEquivPresented R S M k N).trans
    (presentedOperatorsEquiv k N)

/-- Evaluating the differential operator represented by a map out of
principal parts amounts to evaluating that map on the universal class. -/
@[simp, stacks 09CK "principal-parts representation on universal classes"]
theorem representingEquiv_apply_universalDifferential
    (k : ℕ) {N : Type u} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (L : PrincipalParts.module R S M k →ₗ[S] N) (m : M) :
    ((representingEquiv R S M k N L).1 m) =
      L (universalDifferential (R := R) (S := S) (M := M) k m) := by
  rfl

/-- The universal differential into principal parts has differential-operator
order at most its principal-parts order. -/
@[stacks 09CK "universal principal-parts differential has bounded order"]
theorem universalDifferential_isDifferentialOperatorOfOrder (k : ℕ) :
    (universalDifferential (R := R) (S := S) (M := M) k).IsDifferentialOperatorOfOrder S k :=
  by
    let D := representingEquiv R S M k (PrincipalParts.module R S M k)
      (LinearMap.id (R := S) (M := PrincipalParts.module R S M k))
    have hD : (D : M →ₗ[R] PrincipalParts.module R S M k) =
        universalDifferential (R := R) (S := S) (M := M) k := by
      ext m
      simpa [D] using representingEquiv_apply_universalDifferential k
        (LinearMap.id (R := S) (M := PrincipalParts.module R S M k)) m
    simpa [hD] using D.property

/-- Evaluating the map represented by an order-bounded differential operator
on a universal principal-parts class recovers the operator value. -/
@[simp, stacks 09CK "inverse principal-parts representation on universal classes"]
theorem representingEquiv_symm_apply_universalDifferential
    (k : ℕ) {N : Type u} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : differentialOperatorsOrderLE R S M k N) (m : M) :
    (representingEquiv R S M k N).symm D
        (universalDifferential (R := R) (S := S) (M := M) k m) = D.1 m :=
  by
    simpa using (representingEquiv_apply_universalDifferential k
      ((representingEquiv R S M k N).symm D) m).symm

/-- An `S`-linear map out of principal parts is determined by its values on
the universal principal-parts classes. -/
@[ext, stacks 09CK "principal-parts linear-map extensionality"]
theorem linearMap_ext
    (k : ℕ) {N : Type u} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    {L₁ L₂ : PrincipalParts.module R S M k →ₗ[S] N}
    (h : ∀ m : M,
      L₁ (universalDifferential (R := R) (S := S) (M := M) k m) =
        L₂ (universalDifferential (R := R) (S := S) (M := M) k m)) :
    L₁ = L₂ := by
  apply (representingEquiv R S M k N).injective
  ext m
  simpa using h m

-- Proof sketch: both sides are induced by postcomposition with `f` on maps out of
-- `module k`; the bridge from the free presentation to ordinary differential
-- operators is compatible with that postcomposition.
/-- The principal-parts representation of differential operators is functorial in the target
`S`-module. -/
@[stacks 09CK "naturality of the principal-parts representation"]
theorem representingEquiv_natural
    (k : ℕ) {N N' : Type u}
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    (f : N →ₗ[S] N') :
    (differentialOperatorsOrderLE.postcompose (R := R) (S := S) (M₁ := M) f) ∘ₗ
        (representingEquiv
          R S M k N).toLinearMap =
      (representingEquiv
        R S M k N').toLinearMap ∘ₗ
        LinearMap.compRight S f := sorry

end PrincipalParts

end
