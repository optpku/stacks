/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Ring.NegOnePow
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Trace
public import ReasLib.GroupTheory.MonoidExtension.Conjugacy
public import ReasLib.RepresentationTheory.Coinvariants.Complex
public import ReasLib.RepresentationTheory.MonoidAlgebra.Trivial
public import ReasLib.RepresentationTheory.Homological.CoinvariantsResolution
public import ReasLib.RepresentationTheory.Homological.GroupHomology.Finite

/-!
# Alternating traces of coinvariants resolutions

The degree-one generator acts on the coinvariants complex. Its alternating trace
is the trace of the induced endomorphism of the corresponding perfect derived object.
-/

@[expose] public section

open Ring CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidAlgebra Ring
open MonoidAlgebra

noncomputable section

universe u v w

namespace LinearMap.FiniteProjective

section Monoid

variable {Λ : Type u} {G : Type v} {Γ : Type w}
variable [Ring Λ] [Group G] [Monoid Γ] [hFiniteG : Finite G]
variable (S : NatMonoidExtension G Γ)
variable (P : ChainComplex (ModuleCat.{u} (Λ[Γ])) ℕ)
variable [∀ n, Module (Λ[G]) (P.X n)] [∀ n, Module Λ (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[Γ]) (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[G]) (P.X n)]
variable [∀ n, IsRestrictionAlongInl Λ S (P.X n)]
variable [hFinite : ∀ n, Module.Finite (Λ[G]) (P.X n)]
variable [hProjective : ∀ n, Module.Projective (Λ[G]) (P.X n)]

/-- The alternating centralizer trace of a monoid element on a finite segment of a complex. -/
def traceGComplex (r : ℕ) (γ : Γ) : Λ♮ :=
  ∑ i ∈ Finset.range (r + 1), Int.negOnePow (i : ℤ) •
    traceG (smulEndZ S γ : Module.End (Λ[S.centralizer γ]) (P.X i))

/-- The alternating centralizer trace indexed by a degree-one kernel-group conjugacy class. -/
def conjClassTraceComplex (r : ℕ) (c : S.DegreeOneGConjClass) : Λ♮ :=
  ∑ i ∈ Finset.range (r + 1), Int.negOnePow (i : ℤ) • conjClassTrace S (P.X i) c

/-- The class-indexed alternating trace is computed by any representative. -/
theorem conjClassTraceComplex_mk (r : ℕ) (γ : S.degreeOne) :
    conjClassTraceComplex S P r (Quotient.mk (MulAction.orbitRel G S.degreeOne) γ) =
      traceGComplex S P r γ.val := by
  simp only [conjClassTraceComplex, traceGComplex, conjClassTrace_mk]

/-- The alternating trace of the degree-one generator on the coinvariants complex. -/
def trace_oneEndComplex (r : ℕ) : Λ♮ :=
  ∑ i ∈ Finset.range (r + 1),
    Int.negOnePow (i : ℤ) • traceNatural (Coinvariants.oneEnd S (P.X i))

include hFiniteG hFinite hProjective in
/-- Extending the coinvariants complex by zero to cohomological degrees places a
bounded finite-projective complex in the interval from minus its upper bound to zero. -/
theorem coinvariantsCochain_isFiniteProjectiveIn (r : ℕ)
    (hr : ∀ n, r < n → IsZero (P.X n)) :
    CochainComplex.IsFiniteProjectiveIn
      ((Coinvariants.complex S P).extend ComplexShape.embeddingDownNat)
      (-(r : ℤ)) 0 := by
  sorry

include hFiniteG hFinite hProjective in
/-- The derived object of a bounded coinvariants complex is perfect. -/
theorem coinvariantsComplex_isPerfect (r : ℕ)
    (hr : ∀ n, r < n → IsZero (P.X n)) :
    DerivedCategory.IsPerfect
      (DerivedCategory.Q.obj ((Coinvariants.complex S P).extend ComplexShape.embeddingDownNat)) :=
  ⟨_, Iso.refl _, (coinvariantsCochain_isFiniteProjectiveIn S P r hr).isBoundedFiniteProjective⟩

/-- The alternating degree-one trace is the trace of its actual induced perfect derived
endomorphism, without any projectivity assumption on individual homology modules. -/
theorem trace_oneEndComplex_eq_derivedTrace (r : ℕ)
    (hr : ∀ n, r < n → IsZero (P.X n)) :
    trace_oneEndComplex S P r =
      (coinvariantsComplex_isPerfect S P r hr).traceNatural
        (DerivedCategory.Q.map
          (HomologicalComplex.extendMap (Coinvariants.oneEndChainMap S P)
            ComplexShape.embeddingDownNat)) := by
  sorry

end Monoid

section GroupExtension

variable {Λ : Type u} {G : Type v} {E : Type w}
variable [Ring Λ] [Group G] [Group E] [Finite G]
variable (T : GroupExtension G E (Multiplicative ℤ))
variable (P : ChainComplex (ModuleCat.{u} (Λ[NatMonoidExtension.nonneg T])) ℕ)
variable [∀ n, Module (Λ[G]) (P.X n)] [∀ n, Module Λ (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[NatMonoidExtension.nonneg T]) (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[G]) (P.X n)]
variable [∀ n, IsRestrictionAlongInl Λ (NatMonoidExtension.ofGroupExtension T) (P.X n)]
variable [∀ n, Module.Finite (Λ[G]) (P.X n)]
variable [∀ n, Module.Projective (Λ[G]) (P.X n)]

/-- The centralizer order times the alternating centralizer trace on a bounded
resolution of the trivial module is the class of one. -/
theorem traceGComplex_nsmul (r : ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[NatMonoidExtension.nonneg T]))).obj
      (trivialModule Λ (NatMonoidExtension.nonneg T)))
    [QuasiIso ε] (hr : ∀ n, r < n → IsZero (P.X n)) (γ : NatMonoidExtension.nonneg T) :
    Nat.card ((NatMonoidExtension.ofGroupExtension T).centralizer γ) •
      traceGComplex (NatMonoidExtension.ofGroupExtension T) P r γ =
        CommutatorQuotient.mk (1 : Λ) := by
  sorry

/-- When the centralizer order is invertible, its alternating trace on a bounded
resolution of the trivial module is the class of its inverse order. -/
theorem traceGComplex_eq_inv (r : ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[NatMonoidExtension.nonneg T]))).obj
      (trivialModule Λ (NatMonoidExtension.nonneg T)))
    [QuasiIso ε] (hr : ∀ n, r < n → IsZero (P.X n)) (γ : NatMonoidExtension.nonneg T)
    [Invertible (Nat.card ((NatMonoidExtension.ofGroupExtension T).centralizer γ) : Λ)] :
    traceGComplex (NatMonoidExtension.ofGroupExtension T) P r γ =
      CommutatorQuotient.mk
        (⅟(Nat.card ((NatMonoidExtension.ofGroupExtension T).centralizer γ) : Λ)) := by
  sorry

/-- The alternating degree-one trace is the sum of alternating centralizer traces
over kernel-group conjugacy classes of degree-one elements. -/
theorem trace_oneEndComplex_eq_sum_conjClassTrace (r : ℕ) :
    trace_oneEndComplex (NatMonoidExtension.ofGroupExtension T) P r =
      ∑ᶠ c : (NatMonoidExtension.ofGroupExtension T).DegreeOneGConjClass,
        conjClassTraceComplex (NatMonoidExtension.ofGroupExtension T) P r c := by
  sorry

/-- Each degree-one conjugacy-class trace of a bounded trivial-module resolution,
multiplied by its centralizer order, is the class of one. -/
theorem conjClassTraceComplex_nsmul (r : ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[NatMonoidExtension.nonneg T]))).obj
      (trivialModule Λ (NatMonoidExtension.nonneg T)))
    [QuasiIso ε] (hr : ∀ n, r < n → IsZero (P.X n))
    (c : (NatMonoidExtension.ofGroupExtension T).DegreeOneGConjClass) :
    (NatMonoidExtension.ofGroupExtension T).cardCentralizer c •
      conjClassTraceComplex (NatMonoidExtension.ofGroupExtension T) P r c =
        CommutatorQuotient.mk (1 : Λ) := by
  sorry

/-- The degree-one trace on a bounded trivial-module resolution is the sum of
inverse centralizer orders when these orders are coefficient units. -/
theorem trace_oneEndComplex_eq_sum_inv_cardCentralizer (r : ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[NatMonoidExtension.nonneg T]))).obj
      (trivialModule Λ (NatMonoidExtension.nonneg T)))
    [QuasiIso ε] (hr : ∀ n, r < n → IsZero (P.X n))
    (hc : ∀ c : (NatMonoidExtension.ofGroupExtension T).DegreeOneGConjClass,
      IsUnit ((NatMonoidExtension.ofGroupExtension T).cardCentralizer c : Λ)) :
    trace_oneEndComplex (NatMonoidExtension.ofGroupExtension T) P r =
      ∑ᶠ c : (NatMonoidExtension.ofGroupExtension T).DegreeOneGConjClass,
        CommutatorQuotient.mk ((hc c).invertible.invOf : Λ) := by
  sorry

/-- The trace of the induced degree-one endomorphism on the perfect derived
coinvariants object is the sum of inverse centralizer orders. -/
theorem derivedTrace_eq_sum_inv_cardCentralizer (r : ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[NatMonoidExtension.nonneg T]))).obj
      (trivialModule Λ (NatMonoidExtension.nonneg T)))
    [QuasiIso ε] (hr : ∀ n, r < n → IsZero (P.X n))
    (hc : ∀ c : (NatMonoidExtension.ofGroupExtension T).DegreeOneGConjClass,
      IsUnit ((NatMonoidExtension.ofGroupExtension T).cardCentralizer c : Λ)) :
    (coinvariantsComplex_isPerfect (NatMonoidExtension.ofGroupExtension T) P r hr).traceNatural
        (DerivedCategory.Q.map
          (HomologicalComplex.extendMap (Coinvariants.oneEndChainMap (NatMonoidExtension.ofGroupExtension T) P)
            ComplexShape.embeddingDownNat)) =
      ∑ᶠ c : (NatMonoidExtension.ofGroupExtension T).DegreeOneGConjClass,
        CommutatorQuotient.mk ((hc c).invertible.invOf : Λ) :=
  (trace_oneEndComplex_eq_derivedTrace (NatMonoidExtension.ofGroupExtension T) P r hr).symm.trans
    (trace_oneEndComplex_eq_sum_inv_cardCentralizer T P r ε hr hc)

end GroupExtension

section InvertibleOrder

variable {Λ G E : Type u} [CommRing Λ] [Group G] [Group E] [Finite G]
variable (T : GroupExtension G E (Multiplicative ℤ))
variable (P : ChainComplex (ModuleCat.{u} (Λ[NatMonoidExtension.nonneg T])) ℕ)
variable [∀ n, Module (Λ[G]) (P.X n)] [∀ n, Module Λ (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[NatMonoidExtension.nonneg T]) (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[G]) (P.X n)]
variable [∀ n, IsRestrictionAlongInl Λ (NatMonoidExtension.ofGroupExtension T) (P.X n)]
variable [∀ n, Module.Finite (Λ[G]) (P.X n)]
variable [∀ n, Module.Projective (Λ[G]) (P.X n)]

/-- If the finite kernel group's order is a coefficient unit, the degree-one trace
on a bounded trivial-module resolution is the class of one. -/
theorem trace_oneEndComplex_eq_one_of_isUnit_card (r : ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[NatMonoidExtension.nonneg T]))).obj
      (trivialModule Λ (NatMonoidExtension.nonneg T)))
    [QuasiIso ε] (hr : ∀ n, r < n → IsZero (P.X n))
    (hG : IsUnit (Nat.card G : Λ)) :
    trace_oneEndComplex (NatMonoidExtension.ofGroupExtension T) P r =
      CommutatorQuotient.mk (1 : Λ) := by
  sorry

end InvertibleOrder

end LinearMap.FiniteProjective
