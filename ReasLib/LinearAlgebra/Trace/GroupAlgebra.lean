/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import ReasLib.LinearAlgebra.Trace.CommutatorQuotient.FiniteProjective

/-!
# G-trace of a finite projective group-ring module

The identity-coefficient map on `Λ[G]` induces an additive map
`ε : (Λ[G])♮ →+ Λ♮`. Composing it with the finite-projective trace gives
the G-trace of an endomorphism of a finite projective left `Λ[G]`-module.
-/

@[expose] public section

noncomputable section

universe u v w

open Ring
open scoped MonoidAlgebra Ring

namespace MonoidAlgebra

variable {Λ : Type u} {G : Type v} [Ring Λ] [Group G]

/-- The additive map sending a group-ring element to its coefficient at the identity. -/
def coeffOne : Λ[G] →+ Λ :=
  (Finsupp.applyAddHom (1 : G)).comp coeffAddEquiv.toAddMonoidHom

/-- The identity-coefficient map evaluates a group-ring element at the identity. -/
theorem coeffOne_apply (x : Λ[G]) : coeffOne x = x.coeff 1 := sorry

/-- The identity-coefficient map sends the identity basis element with coefficient `r` to `r`. -/
theorem coeffOne_single_one (r : Λ) : coeffOne (single (1 : G) r) = r := sorry

/-- The identity-coefficient map vanishes on off-identity basis elements. -/
theorem coeffOne_single_of_ne {g : G} (hg : g ≠ 1) (r : Λ) :
    coeffOne (single g r) = 0 := sorry

/-- The identity-coefficient map composed with the canonical projection to `Λ♮`. -/
def epsilonPre : Λ[G] →+ Λ♮ :=
  CommutatorQuotient.mk.comp coeffOne

/-- The pre-descent map sends a group-ring element to the class of its identity coefficient. -/
theorem epsilonPre_apply (x : Λ[G]) :
    epsilonPre x = CommutatorQuotient.mk (x.coeff 1) := sorry

/-- The identity-coefficient map vanishes on additive ring commutators. -/
theorem epsilonPre_commutatorAddSubgroup_le_ker :
    Ring.commutatorAddSubgroup (Λ[G]) ≤
      (epsilonPre : Λ[G] →+ Λ♮).ker := sorry

/-- The additive map `ε : (Λ[G])♮ →+ Λ♮` induced by the identity-coefficient map. -/
noncomputable def epsilon : (Λ[G])♮ →+ Λ♮ :=
  QuotientAddGroup.lift (Ring.commutatorAddSubgroup (Λ[G])) epsilonPre
    epsilonPre_commutatorAddSubgroup_le_ker

/-- On representatives, `ε` recovers the identity-coefficient map into `Λ♮`. -/
theorem epsilon_mk (x : Λ[G]) :
    epsilon (CommutatorQuotient.mk x) = epsilonPre x := sorry

/-- An additive map `(Λ[G])♮ →+ Λ♮` that recovers the class of the identity
coefficient on representatives equals `epsilon`. -/
theorem epsilon_unique (φ : (Λ[G])♮ →+ Λ♮)
    (h : ∀ x, φ (CommutatorQuotient.mk x) = CommutatorQuotient.mk (x.coeff 1)) :
    φ = epsilon := sorry

end MonoidAlgebra

/-- A finite module over a finite group ring is finite over its coefficient ring. -/
theorem Module.Finite.of_restrictScalars_monoidAlgebra
    (Λ : Type u) (G : Type v) (P : Type w) [Ring Λ] [Group G] [Finite G]
    [AddCommGroup P] [Module (Λ[G]) P] [Module Λ P] [IsScalarTower Λ (Λ[G]) P]
    [Module.Finite (Λ[G]) P] : Module.Finite Λ P := sorry

/-- A projective module over a finite group ring is projective over its coefficient ring. -/
theorem Module.Projective.of_restrictScalars_monoidAlgebra
    (Λ : Type u) (G : Type v) (P : Type w) [Ring Λ] [Group G] [Finite G]
    [AddCommGroup P] [Module (Λ[G]) P] [Module Λ P] [IsScalarTower Λ (Λ[G]) P]
    [Module.Projective (Λ[G]) P] : Module.Projective Λ P := sorry

namespace LinearMap.FiniteProjective

variable {Λ : Type u} {G : Type v} [Ring Λ] [Group G]
variable {P : Type w} [AddCommGroup P] [Module (Λ[G]) P]
variable [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P]

/-- The G-trace of an endomorphism of a finite projective left `Λ[G]`-module,
as an additive map into `Λ♮`. -/
noncomputable def traceG : Module.End (Λ[G]) P →+ Λ♮ :=
  MonoidAlgebra.epsilon.comp
    (traceNatural : Module.End (Λ[G]) P →+ (Λ[G])♮)

/-- The G-trace is `ε` of the finite-projective trace over `Λ[G]`. -/
theorem traceG_apply (f : Module.End (Λ[G]) P) :
    traceG f = MonoidAlgebra.epsilon
      ((traceNatural : Module.End (Λ[G]) P →+ (Λ[G])♮) f) := sorry

/-- The finite-projective trace over the coefficient ring of a finite group ring,
computed by restricting scalars on an endomorphism of a finite projective module. -/
noncomputable def traceNatural_restrictScalars
    {Λ : Type u} {G : Type v} {P : Type w}
    [Ring Λ] [Group G] [Finite G]
    [AddCommGroup P] [Module (Λ[G]) P] [Module Λ P] [IsScalarTower Λ (Λ[G]) P]
    [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P]
    (f : Module.End (Λ[G]) P) : Λ♮ :=
  -- Local instance justification (proof-local temporary data): Fix the group in the derived finiteness fact, since the conclusion cannot infer it.
  letI : Module.Finite Λ P := Module.Finite.of_restrictScalars_monoidAlgebra Λ G P
  -- Local instance justification (proof-local temporary data): Fix the group in the derived projectivity fact, since the conclusion cannot infer it.
  letI : Module.Projective Λ P := Module.Projective.of_restrictScalars_monoidAlgebra Λ G P
  traceNatural (f.restrictScalars Λ)

/-- The trace over the coefficient ring of an endomorphism of a finite projective
group-ring module is the group cardinality times its G-trace in the additive
commutator quotient. -/
theorem traceNatural_eq_card_smul_traceG
    {Λ : Type u} {G : Type v} {P : Type w}
    [Ring Λ] [Group G] [Finite G]
    [AddCommGroup P] [Module (Λ[G]) P] [Module Λ P] [IsScalarTower Λ (Λ[G]) P]
    [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P]
    (f : Module.End (Λ[G]) P) :
    traceNatural_restrictScalars f = Nat.card G • traceG f := sorry

end LinearMap.FiniteProjective
