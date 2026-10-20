/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.LinearAlgebra.Trace.CoinvariantsComplex

/-!
# The trivial trace formula for a finite group

A finite projective resolution of the trivial module computes group homology
and Tor after taking kernel-group coinvariants. The action of the degree-one
generator has the displayed centralizer trace formula on the associated perfect
derived object. This gives a point-count interpretation on `BG`; over a field
of characteristic prime to the group order the weighted count equals one.
The later trace formula (64.14.3.1) and Section 64.30 give further interpretations.
-/

open Ring CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidAlgebra Ring
open MonoidAlgebra

universe u v w

section Traces

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

/- Remark 64.15.10
The degree-one generator acts on the perfect derived coinvariants object of the
bounded resolution. Its trace is the sum of inverse centralizer orders.
-/
@[stacks 03UE] #check
  (LinearMap.FiniteProjective.derivedTrace_eq_sum_inv_cardCentralizer T P :
    ∀ (r : ℕ)
      (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[NatMonoidExtension.nonneg T]))).obj
        (trivialModule Λ (NatMonoidExtension.nonneg T)))
      [QuasiIso ε] (hr : ∀ n, r < n → IsZero (P.X n))
      (hc : ∀ c : (NatMonoidExtension.ofGroupExtension T).DegreeOneGConjClass,
        IsUnit ((NatMonoidExtension.ofGroupExtension T).cardCentralizer c : Λ)),
      (LinearMap.FiniteProjective.coinvariantsComplex_isPerfect
          (NatMonoidExtension.ofGroupExtension T) P r hr).traceNatural
        (DerivedCategory.Q.map
          (HomologicalComplex.extendMap (Coinvariants.oneEndChainMap (NatMonoidExtension.ofGroupExtension T) P)
            ComplexShape.embeddingDownNat)) =
        ∑ᶠ c : (NatMonoidExtension.ofGroupExtension T).DegreeOneGConjClass,
          CommutatorQuotient.mk ((hc c).invertible.invOf : Λ))

#check (LinearMap.FiniteProjective.traceGComplex_nsmul T P :
  ∀ (r : ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[NatMonoidExtension.nonneg T]))).obj
      (trivialModule Λ (NatMonoidExtension.nonneg T)))
    [QuasiIso ε] (hr : ∀ n, r < n → IsZero (P.X n)) (γ : NatMonoidExtension.nonneg T),
    Nat.card ((NatMonoidExtension.ofGroupExtension T).centralizer γ) •
      LinearMap.FiniteProjective.traceGComplex (NatMonoidExtension.ofGroupExtension T) P r γ =
        CommutatorQuotient.mk (1 : Λ))

#check (LinearMap.FiniteProjective.traceGComplex_eq_inv T P :
  ∀ (r : ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[NatMonoidExtension.nonneg T]))).obj
      (trivialModule Λ (NatMonoidExtension.nonneg T)))
    [QuasiIso ε] (hr : ∀ n, r < n → IsZero (P.X n)) (γ : NatMonoidExtension.nonneg T)
    [Invertible (Nat.card ((NatMonoidExtension.ofGroupExtension T).centralizer γ) : Λ)],
    LinearMap.FiniteProjective.traceGComplex (NatMonoidExtension.ofGroupExtension T) P r γ =
      CommutatorQuotient.mk
        (⅟(Nat.card ((NatMonoidExtension.ofGroupExtension T).centralizer γ) : Λ)))

#check (LinearMap.FiniteProjective.trace_oneEndComplex_eq_sum_conjClassTrace T P :
  ∀ r : ℕ,
    LinearMap.FiniteProjective.trace_oneEndComplex (NatMonoidExtension.ofGroupExtension T) P r =
      ∑ᶠ c : (NatMonoidExtension.ofGroupExtension T).DegreeOneGConjClass,
        LinearMap.FiniteProjective.conjClassTraceComplex
          (NatMonoidExtension.ofGroupExtension T) P r c)

#check (LinearMap.FiniteProjective.conjClassTraceComplex_nsmul T P :
  ∀ (r : ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[NatMonoidExtension.nonneg T]))).obj
      (trivialModule Λ (NatMonoidExtension.nonneg T)))
    [QuasiIso ε] (hr : ∀ n, r < n → IsZero (P.X n))
    (c : (NatMonoidExtension.ofGroupExtension T).DegreeOneGConjClass),
    (NatMonoidExtension.ofGroupExtension T).cardCentralizer c •
      LinearMap.FiniteProjective.conjClassTraceComplex
        (NatMonoidExtension.ofGroupExtension T) P r c = CommutatorQuotient.mk (1 : Λ))

#check (LinearMap.FiniteProjective.trace_oneEndComplex_eq_sum_inv_cardCentralizer T P :
  ∀ (r : ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[NatMonoidExtension.nonneg T]))).obj
      (trivialModule Λ (NatMonoidExtension.nonneg T)))
    [QuasiIso ε] (hr : ∀ n, r < n → IsZero (P.X n))
    (hc : ∀ c : (NatMonoidExtension.ofGroupExtension T).DegreeOneGConjClass,
      IsUnit ((NatMonoidExtension.ofGroupExtension T).cardCentralizer c : Λ)),
    LinearMap.FiniteProjective.trace_oneEndComplex (NatMonoidExtension.ofGroupExtension T) P r =
      ∑ᶠ c : (NatMonoidExtension.ofGroupExtension T).DegreeOneGConjClass,
        CommutatorQuotient.mk ((hc c).invertible.invOf : Λ))

#check (LinearMap.FiniteProjective.trace_oneEndComplex_eq_derivedTrace
  (NatMonoidExtension.ofGroupExtension T) P :
  ∀ (r : ℕ) (hr : ∀ n, r < n → IsZero (P.X n)),
    LinearMap.FiniteProjective.trace_oneEndComplex (NatMonoidExtension.ofGroupExtension T) P r =
      (LinearMap.FiniteProjective.coinvariantsComplex_isPerfect
          (NatMonoidExtension.ofGroupExtension T) P r hr).traceNatural
        (DerivedCategory.Q.map
          (HomologicalComplex.extendMap (Coinvariants.oneEndChainMap (NatMonoidExtension.ofGroupExtension T) P)
            ComplexShape.embeddingDownNat)))

end Traces

section DerivedCoinvariants

variable {Λ G Γ : Type u} [Ring Λ] [Group G] [Monoid Γ] [Finite G]
variable (S : NatMonoidExtension G Γ)
variable (P : ChainComplex (ModuleCat.{u} (Λ[Γ])) ℕ)
variable [∀ n, Module (Λ[G]) (P.X n)] [∀ n, Module Λ (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[Γ]) (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[G]) (P.X n)]
variable [∀ n, IsRestrictionAlongInl Λ S (P.X n)]
variable [∀ n, Module.Finite (Λ[G]) (P.X n)]
variable [∀ n, Module.Projective (Λ[G]) (P.X n)]

#check (MonoidAlgebra.Coinvariants.homologyIso_leftDerived S P :
  ∀ (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] (n : ℕ),
    (Coinvariants.complex S P).homology n ≅
      ((Coinvariants.functor Λ G).leftDerived n).obj (trivialModule Λ G))

end DerivedCoinvariants

section Homology

variable {Λ G Γ : Type u} [CommRing Λ] [Group G] [Monoid Γ] [Finite G]
variable (S : NatMonoidExtension G Γ)
variable (P : ChainComplex (ModuleCat.{u} (Λ[Γ])) ℕ)
variable [∀ n, Module (Λ[G]) (P.X n)] [∀ n, Module Λ (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[Γ]) (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[G]) (P.X n)]
variable [∀ n, IsRestrictionAlongInl Λ S (P.X n)]
variable [∀ n, Module.Finite (Λ[G]) (P.X n)]
variable [∀ n, Module.Projective (Λ[G]) (P.X n)]

#check (MonoidAlgebra.Coinvariants.homologyIso S P :
  ∀ (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] (n : ℕ),
    (Coinvariants.complex S P).homology n ≅ groupHomology (Rep.trivial Λ G Λ) n)

#check (MonoidAlgebra.Coinvariants.homologyIso_tor S P :
  ∀ (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] (n : ℕ),
    (Coinvariants.complex S P).homology n ≅
      ((Rep.Tor Λ G n).obj (Rep.trivial Λ G Λ)).obj (Rep.trivial Λ G Λ))

open Classical in
#check (groupHomologyIsoTor (Rep.trivial Λ G Λ) :
  ∀ n : ℕ, groupHomology (Rep.trivial Λ G Λ) n ≅
    ((Rep.Tor Λ G n).obj (Rep.trivial Λ G Λ)).obj (Rep.trivial Λ G Λ))

#check (groupHomology.isZero_trivial_succ_of_isUnit_card (Λ := Λ) (G := G) :
  ∀ (_ : IsUnit (Nat.card G : Λ)) (n : ℕ),
    IsZero (groupHomology (Rep.trivial Λ G Λ) (n + 1)))

#check (groupHomology.H0IsoOfIsTrivial (Rep.trivial Λ G Λ) :
  groupHomology (Rep.trivial Λ G Λ) 0 ≅ ModuleCat.of Λ Λ)

#check (groupHomology.H0IsoOfIsTrivial_inv_eq_π (Rep.trivial Λ G Λ) :
  (groupHomology.H0IsoOfIsTrivial (Rep.trivial Λ G Λ)).inv =
    groupHomology.H0π (Rep.trivial Λ G Λ))

end Homology

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

#check (LinearMap.FiniteProjective.trace_oneEndComplex_eq_one_of_isUnit_card T P :
  ∀ (r : ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[NatMonoidExtension.nonneg T]))).obj
      (trivialModule Λ (NatMonoidExtension.nonneg T)))
    [QuasiIso ε] (hr : ∀ n, r < n → IsZero (P.X n)) (_ : IsUnit (Nat.card G : Λ)),
    LinearMap.FiniteProjective.trace_oneEndComplex (NatMonoidExtension.ofGroupExtension T) P r =
      CommutatorQuotient.mk (1 : Λ))

end InvertibleOrder

section Counting

variable {G : Type v} {E : Type w} [Group G] [Group E] [Finite G]
variable (T : GroupExtension G E (Multiplicative ℤ))

#check (NatMonoidExtension.one_eq_sum_inv_cardCentralizer T :
  ∀ {Λ : Type u} [Field Λ] (_ : IsUnit (Nat.card G : Λ)),
    (1 : Λ) = ∑ᶠ c : (NatMonoidExtension.ofGroupExtension T).DegreeOneGConjClass,
      ((NatMonoidExtension.ofGroupExtension T).cardCentralizer c : Λ)⁻¹)

#check (NatMonoidExtension.one_eq_sum_inv_cardCentralizer_zmod T :
  ∀ {ℓ : ℕ} [Fact ℓ.Prime] (_ : IsUnit (Nat.card G : ZMod ℓ)),
    (1 : ZMod ℓ) = ∑ᶠ c : (NatMonoidExtension.ofGroupExtension T).DegreeOneGConjClass,
      ((NatMonoidExtension.ofGroupExtension T).cardCentralizer c : ZMod ℓ)⁻¹)

end Counting
