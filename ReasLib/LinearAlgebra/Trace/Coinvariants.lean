/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Nat.Hom
public import ReasLib.LinearAlgebra.Trace.GroupAlgebra
public import ReasLib.RepresentationTheory.Coinvariants
public import ReasLib.RepresentationTheory.MonoidAlgebra.Restriction

/-!
# Traces of natural-number actions on coinvariants

The degree-one action descends to coinvariants independently of its chosen lift.
Its trace is a sum of centralizer traces indexed by kernel-group conjugacy classes.
-/

@[expose] public section

noncomputable section

universe u v w x

open Ring
open scoped MonoidAlgebra Ring

namespace LinearMap.FiniteProjective

variable {Λ : Type u} {G : Type v} {Γ : Type w}
variable [Ring Λ] [Group G] [Monoid Γ] [Finite G]
variable (S : NatMonoidExtension G Γ) (P : Type x)
variable [AddCommGroup P] [Module (Λ[Γ]) P] [Module (Λ[G]) P] [Module Λ P]
variable [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P]

/-- Kernel-group conjugate degree-one elements have equal centralizer traces. -/
theorem gConj_traceG_eq
    [IsScalarTower Λ (Λ[G]) P] [IsScalarTower Λ (Λ[Γ]) P]
    [MonoidAlgebra.IsRestrictionAlongInl Λ S P]
    {γ γ' : S.degreeOne}
    (h : MulAction.orbitRel G S.degreeOne γ γ') :
    traceG (smulEndZ S γ.val : Module.End (Λ[S.centralizer γ.val]) P) =
      traceG (smulEndZ S γ'.val : Module.End (Λ[S.centralizer γ'.val]) P) := sorry

/-- The centralizer trace as a function of a kernel-group conjugacy class of degree-one elements. -/
def conjClassTrace
    [IsScalarTower Λ (Λ[G]) P] [IsScalarTower Λ (Λ[Γ]) P]
    [MonoidAlgebra.IsRestrictionAlongInl Λ S P] :
    S.DegreeOneGConjClass → Λ♮ :=
  Quotient.lift
    (fun γ : S.degreeOne ↦
      traceG (smulEndZ S γ.val : Module.End (Λ[S.centralizer γ.val]) P))
    (fun _ _ h ↦ gConj_traceG_eq S P h)

/-- The trace of a degree-one conjugacy class is the centralizer trace of any representative. -/
theorem conjClassTrace_mk
    [IsScalarTower Λ (Λ[G]) P] [IsScalarTower Λ (Λ[Γ]) P]
    [MonoidAlgebra.IsRestrictionAlongInl Λ S P] (γ : S.degreeOne) :
    conjClassTrace S P (Quotient.mk (MulAction.orbitRel G S.degreeOne) γ) =
      traceG (smulEndZ S γ.val : Module.End (Λ[S.centralizer γ.val]) P) := rfl

end LinearMap.FiniteProjective

namespace MonoidAlgebra.Coinvariants

variable {Λ : Type u} {G : Type v} {Γ : Type w}
variable [Ring Λ] [Group G] [Monoid Γ]
variable (S : NatMonoidExtension G Γ) (P : Type x)
variable [AddCommGroup P] [Module (Λ[Γ]) P] [Module (Λ[G]) P] [Module Λ P]
variable [IsScalarTower Λ (Λ[G]) P]
variable [IsScalarTower Λ (Λ[Γ]) P] [IsRestrictionAlongInl Λ S P]

/-- The degree-one action followed by the coinvariant quotient is invariant under the kernel group. -/
theorem oneEnd_invariant (g : G) (p : P) :
    ((mk Λ G P).comp (LinearMap.FiniteProjective.smulEnd S.degreeOneLift.val))
        ((single g (1 : Λ) : Λ[G]) • p) =
      ((mk Λ G P).comp (LinearMap.FiniteProjective.smulEnd S.degreeOneLift.val)) p := by
  have hinl : S.rightHom (S.inl g) = 1 := by
    have hg : S.inl g ∈ MonoidHom.mrange S.inl := ⟨g, rfl⟩
    rw [S.range_inl_eq_ker_rightHom] at hg
    exact hg
  obtain ⟨h, hh, _⟩ := S.eqDegree_leftTorsor S.degreeOneLift.val
    (S.degreeOneLift.val * S.inl g) (by simp only [map_mul, hinl, mul_one])
  change mk Λ G P ((single S.degreeOneLift.val (1 : Λ) : Λ[Γ]) •
      ((single g (1 : Λ) : Λ[G]) • p)) =
    mk Λ G P ((single S.degreeOneLift.val (1 : Λ) : Λ[Γ]) • p)
  have hsmul : (single S.degreeOneLift.val (1 : Λ) : Λ[Γ]) •
        ((single g (1 : Λ) : Λ[G]) • p) =
      (single h (1 : Λ) : Λ[G]) •
        ((single S.degreeOneLift.val (1 : Λ) : Λ[Γ]) • p) := by
    rw [IsRestrictionAlongInl.smul_single S g p,
      IsRestrictionAlongInl.smul_single S h _, ← mul_smul, ← mul_smul]
    simp only [single_mul_single, one_mul, hh]
  rw [hsmul]
  apply (Submodule.Quotient.eq (ker Λ G P)).mpr
  exact Submodule.subset_span
    ⟨(h, (single S.degreeOneLift.val (1 : Λ) : Λ[Γ]) • p), rfl⟩

/-- The descended coefficient-linear degree-one action on coinvariants. -/
def oneEnd : Module.End Λ (Coinvariants Λ G P) :=
  lift Λ G P ((mk Λ G P).comp (LinearMap.FiniteProjective.smulEnd S.degreeOneLift.val))
    (oneEnd_invariant S P)

/-- Every degree-one lift gives the same action on coinvariant classes. -/
theorem oneEnd_spec (γ : S.degreeOne) (p : P) :
    (oneEnd S P : Module.End Λ (Coinvariants Λ G P)) (mk Λ G P p) =
      mk Λ G P ((LinearMap.FiniteProjective.smulEnd γ.val : Module.End Λ P) p) := by
  have hdeg : S.rightHom S.degreeOneLift.val = S.rightHom γ.val :=
    congrArg Multiplicative.ofAdd (S.degreeOneLift.property.trans γ.property.symm)
  obtain ⟨g, hg, _⟩ := S.eqDegree_leftTorsor S.degreeOneLift.val γ.val hdeg
  change mk Λ G P ((single S.degreeOneLift.val (1 : Λ) : Λ[Γ]) • p) =
    mk Λ G P ((single γ.val (1 : Λ) : Λ[Γ]) • p)
  rw [hg]
  have hsmul : (single (S.inl g * S.degreeOneLift.val) (1 : Λ) : Λ[Γ]) • p =
      (single g (1 : Λ) : Λ[G]) •
        ((single S.degreeOneLift.val (1 : Λ) : Λ[Γ]) • p) := by
    rw [IsRestrictionAlongInl.smul_single S g _, ← mul_smul,
      single_mul_single, one_mul]
  rw [hsmul]
  symm
  apply (Submodule.Quotient.eq (ker Λ G P)).mpr
  exact Submodule.subset_span
    ⟨(g, (single S.degreeOneLift.val (1 : Λ) : Λ[Γ]) • p), rfl⟩

/-- The endomorphism for a natural number is the corresponding power of the degree-one action. -/
def natEnd (n : ℕ) : Module.End Λ (Coinvariants Λ G P) :=
  oneEnd S P ^ n

/-- The natural-number action on coinvariants, bundled as a monoid homomorphism. -/
def natAction : Multiplicative ℕ →* Module.End Λ (Coinvariants Λ G P) :=
  powersHom (Module.End Λ (Coinvariants Λ G P)) (oneEnd S P)

/-- The bundled natural-number action agrees with the power formula. -/
theorem natAction_apply (n : ℕ) :
    (natAction S P (Multiplicative.ofAdd n) : Module.End Λ (Coinvariants Λ G P)) =
      natEnd S P n := rfl

end MonoidAlgebra.Coinvariants

namespace LinearMap.FiniteProjective

/-- For the nonnegative part of an integer group extension with finite kernel, the trace
of the degree-one action on coinvariants equals the sum of centralizer traces over
kernel-group conjugacy classes of degree-one elements. -/
theorem trace_one_coinvariants
    {Λ : Type u} {G : Type v} {E : Type w} [Ring Λ] [Group G] [Group E] [Finite G]
    (T : GroupExtension G E (Multiplicative ℤ)) (P : Type x)
    [AddCommGroup P] [Module (Λ[NatMonoidExtension.nonneg T]) P]
    [Module (Λ[G]) P] [Module Λ P]
    [IsScalarTower Λ (Λ[G]) P] [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P]
    [IsScalarTower Λ (Λ[NatMonoidExtension.nonneg T]) P]
    [MonoidAlgebra.IsRestrictionAlongInl Λ (NatMonoidExtension.ofGroupExtension T) P] :
    (traceNatural (MonoidAlgebra.Coinvariants.oneEnd (NatMonoidExtension.ofGroupExtension T) P) : Λ♮) =
      ∑ᶠ c : (NatMonoidExtension.ofGroupExtension T).DegreeOneGConjClass,
        conjClassTrace (NatMonoidExtension.ofGroupExtension T) P c := sorry

end LinearMap.FiniteProjective
