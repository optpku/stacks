/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Ring.NegOnePow
public import stacks_project.Chap64.Lemma_64_15_9

/-!
# Alternating traces on a bounded complex of finite projective modules

This leaf owns the well-defined cardinality `#Z_γ` of a degree-1 `G`-conjugacy
class and the alternating `Z_γ`-trace, class trace, and coinvariants identity
trace of a bounded `ℕ`-indexed complex.
-/

@[expose] public section

open Ring
open scoped MonoidAlgebra Ring
open MonoidAlgebra LinearMap.FiniteProjective

noncomputable section

universe u v w

namespace NatMonoidExtension

variable {G : Type v} {Γ : Type w} [Group G] [Monoid Γ] (S : NatMonoidExtension G Γ)

/-- Conjugate degree-1 elements have centralizers of equal finite cardinality. -/
theorem card_centralizer_eq_of_isGConj {γ γ' : S.degreeOne}
    (h : MulAction.orbitRel G S.degreeOne γ γ') :
    Nat.card (S.centralizer γ.val) = Nat.card (S.centralizer γ'.val) :=
  sorry

/-- The cardinality of `Z_γ`, as a well-defined function of the `G`-conjugacy
class of a degree-1 element. -/
noncomputable def cardCentralizer : S.DegreeOneGConjClass → ℕ :=
  Quotient.lift (fun γ : S.degreeOne ↦ Nat.card (S.centralizer γ.val))
    fun _ _ h ↦ S.card_centralizer_eq_of_isGConj h

/-- On a representative, `cardCentralizer` recovers `#Z_γ`. -/
theorem cardCentralizer_mk (γ : S.degreeOne) :
    cardCentralizer S (Quotient.mk (MulAction.orbitRel G S.degreeOne) γ) =
      Nat.card (S.centralizer γ.val) :=
  sorry

end NatMonoidExtension

namespace LinearMap.FiniteProjective

variable {Λ : Type u} {G : Type v} {Γ : Type w}
variable [Ring Λ] [Group G] [Monoid Γ] [Finite G]
variable (S : NatMonoidExtension G Γ)
variable (P : ChainComplex (ModuleCat.{u} (Λ[Γ])) ℕ)
variable [∀ n, Module (Λ[G]) (P.X n)] [∀ n, Module Λ (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[Γ]) (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[G]) (P.X n)]
variable [∀ n, IsRestrictionAlongInl Λ S (P.X n)]
variable [∀ n, Module.Finite (Λ[G]) (P.X n)]
variable [∀ n, Module.Projective (Λ[G]) (P.X n)]

/-- The alternating `Z_γ`-trace of the action of `γ` on a bounded complex of
finite projective `Λ[G]`-modules, valued in `Λ♮`. -/
noncomputable def traceGComplex (r : ℕ) (γ : Γ) : Λ♮ :=
  ∑ i ∈ Finset.range (r + 1),
    Int.negOnePow (i : ℤ) •
      traceG (smulEndZ S γ : Module.End (Λ[S.centralizer γ]) (P.X i))

/-- The alternating class trace of a `G`-conjugacy class of degree-1 elements
on a bounded complex. -/
noncomputable def conjClassTraceComplex (r : ℕ) (c : S.DegreeOneGConjClass) : Λ♮ :=
  ∑ i ∈ Finset.range (r + 1), Int.negOnePow (i : ℤ) • conjClassTrace S (P.X i) c

/-- The class trace of a degree-1 representative is the alternating `Z_γ`-trace
of that element. -/
theorem conjClassTraceComplex_mk (r : ℕ) (γ : S.degreeOne) :
    conjClassTraceComplex S P r (Quotient.mk (MulAction.orbitRel G S.degreeOne) γ) =
      traceGComplex S P r γ.val :=
  sorry

/-- The alternating finite-projective trace of the action of `1 ∈ ℕ` on the
coinvariants complex `(P_•)_G`. -/
noncomputable def trace_oneEndComplex (r : ℕ) : Λ♮ :=
  ∑ i ∈ Finset.range (r + 1),
    Int.negOnePow (i : ℤ) • traceNatural (Coinvariants.oneEnd S (P.X i))

/-- If `#G` is a unit in `Λ`, then `#Z_γ` is a unit in `Λ`. -/
theorem isUnit_cardCentralizer (hG : IsUnit (Nat.card G : Λ))
    (c : S.DegreeOneGConjClass) :
    IsUnit (S.cardCentralizer c : Λ) :=
  sorry

end LinearMap.FiniteProjective
