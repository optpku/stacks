/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.DifferentialOperator.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# First-Order Differential Operators on an Algebra

This leaf packages the canonical decomposition of a first-order differential
operator from an algebra into an `S`-module.  The two components are its value
at `1` and the derivation obtained after removing multiplication by that value.
The construction is independent of principal-parts presentations.

@stack 09CM
-/

@[expose] public section

universe u v w w'

noncomputable section

open KaehlerDifferential

namespace DifferentialOperator.FirstOrder

section Decomposition

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup N] [Module S N] [Module R N]
variable [IsScalarTower R S N]

/-- The multiplication operator `s ↦ s • x`, regarded as an `R`-linear map. -/
def multiplication (x : N) : S →ₗ[R] N :=
  LinearMap.smulRight (LinearMap.id : S →ₗ[R] S) x

/-- The `R`-linear map obtained by removing the value-at-one multiplication operator from `D`. -/
def derivationLinear (D : differentialOperatorsOrderLE R S S 1 N) : S →ₗ[R] N :=
  D.1 - multiplication (R := R) (S := S) (N := N) (D.1 1)

/-- The corrected linear map of a first-order differential operator satisfies the Leibniz rule. -/
theorem derivationLinear_leibniz (D : differentialOperatorsOrderLE R S S 1 N) (g h : S) :
    derivationLinear (R := R) (S := S) (N := N) D (g * h) =
      g • derivationLinear (R := R) (S := S) (N := N) D h +
        h • derivationLinear (R := R) (S := S) (N := N) D g := sorry

/-- The derivation component of a first-order differential operator. -/
def derivationPart (D : differentialOperatorsOrderLE R S S 1 N) : Derivation R S N :=
  Derivation.mk'
    (derivationLinear (R := R) (S := S) (N := N) D)
    (derivationLinear_leibniz (R := R) (S := S) (N := N) D)

/-- A derivation plus multiplication by a value is a first-order differential operator. -/
theorem fromDerivationProd_mem (p : Derivation R S N × N) :
    LinearMap.IsDifferentialOperatorOfOrder
      (p.1.toLinearMap + multiplication (R := R) (S := S) (N := N) p.2) S 1 := sorry

/-- Recombine a derivation and a value-at-one component as an `S`-linear map. -/
def fromDerivationProd :
    (Derivation R S N × N) →ₗ[S] differentialOperatorsOrderLE R S S 1 N where
  toFun p :=
    ⟨p.1.toLinearMap + multiplication (R := R) (S := S) (N := N) p.2,
      fromDerivationProd_mem (R := R) (S := S) (N := N) p⟩
  map_add' := sorry
  map_smul' := sorry

/-- The decomposition into derivation and value-at-one components, as an `S`-linear map. -/
def toDerivationProd :
    differentialOperatorsOrderLE R S S 1 N →ₗ[S] Derivation R S N × N where
  toFun D := (derivationPart (R := R) (S := S) (N := N) D, D.1 1)
  map_add' := sorry
  map_smul' := sorry

/-- Decomposing after recombining a derivation and a value gives the original pair. -/
theorem toDerivationProd_comp_from :
    (toDerivationProd (R := R) (S := S) (N := N)).comp
        (fromDerivationProd (R := R) (S := S) (N := N)) =
      (LinearMap.id : (Derivation R S N × N) →ₗ[S] Derivation R S N × N) := sorry

/-- Recombining the components of a first-order differential operator recovers that operator. -/
theorem fromDerivationProd_comp_to :
    (fromDerivationProd (R := R) (S := S) (N := N)).comp
        (toDerivationProd (R := R) (S := S) (N := N)) =
      (LinearMap.id : differentialOperatorsOrderLE R S S 1 N →ₗ[S]
        differentialOperatorsOrderLE R S S 1 N) := sorry

/-- Example 10.133.5 (1), tag 09CM: first-order differential operators from `S` to `N`
are canonically the product of `R`-derivations `S → N` and values in `N`. -/
@[stacks 09CM]
def equivDerivationProd :
    differentialOperatorsOrderLE R S S 1 N ≃ₗ[S] Derivation R S N × N :=
  LinearEquiv.ofLinear
    (toDerivationProd (R := R) (S := S) (N := N))
    (fromDerivationProd (R := R) (S := S) (N := N))
    (toDerivationProd_comp_from (R := R) (S := S) (N := N))
    (fromDerivationProd_comp_to (R := R) (S := S) (N := N))

/-- Example 10.133.5 (2), tag 09CM: via Kähler differentials, first-order differential
operators from `S` to `N` are the product of `S`-linear maps `Ω[S⁄R] → N` and values in `N`. -/
@[stacks 09CM]
noncomputable def equivCotangentProd :
    differentialOperatorsOrderLE R S S 1 N ≃ₗ[S] (Ω[S⁄R] →ₗ[S] N) × N :=
  (equivDerivationProd (R := R) (S := S) (N := N)).trans
    ((linearMapEquivDerivation R S).symm.prodCongr (LinearEquiv.refl S N))

end Decomposition

section Naturality

variable {R : Type u} {S : Type v} {N : Type w} {N' : Type w'}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup N] [Module S N] [Module R N]
variable [IsScalarTower R S N]
variable [AddCommGroup N'] [Module S N'] [Module R N']
variable [IsScalarTower R S N']

/-- The derivation-and-value decomposition is natural under `S`-linear postcomposition. -/
theorem toDerivationProd_natural (f : N →ₗ[S] N')
    (D : differentialOperatorsOrderLE R S S 1 N) :
    toDerivationProd (R := R) (S := S) (N := N')
        (differentialOperatorsOrderLE.postcompose (R := R) (S := S) (M₁ := S) f D) =
      (f.compDer (derivationPart (R := R) (S := S) (N := N) D), f (D.1 1)) := sorry

/-- The cotangent-and-value decomposition is natural under `S`-linear postcomposition. -/
theorem equivCotangentProd_natural (f : N →ₗ[S] N')
    (D : differentialOperatorsOrderLE R S S 1 N) :
    equivCotangentProd (R := R) (S := S) (N := N')
        (differentialOperatorsOrderLE.postcompose (R := R) (S := S) (M₁ := S) f D) =
      ((LinearMap.compRight S f)
          (equivCotangentProd (R := R) (S := S) (N := N) D).1,
        f (equivCotangentProd (R := R) (S := S) (N := N) D).2) := sorry

end Naturality

end DifferentialOperator.FirstOrder
