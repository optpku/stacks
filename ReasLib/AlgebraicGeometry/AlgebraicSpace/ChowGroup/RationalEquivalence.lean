/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.DeltaDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.ClosedPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.WeilDivisor


/-!
# Rational equivalence of cycles on algebraic spaces

For a good algebraic space, a locally finite family of integral
closed subspaces of δ-dimension `k + 1` together with rational units determines
a `k`-cycle by pushing forward principal Weil divisors. Rational equivalence is
the resulting subgroup of `Z_k(X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open Function Set Topology

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

namespace RationalEquivalence

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]

/-- The principal Weil divisor of a rational unit on an integral closed subspace,
formed after transporting locally Noetherianity along `W.ι ≫ f`. -/
noncomputable def principalDivisor (W : ClosedSubspace X) [IsIntegral W.X]
    (φ : (RationalFunction W.X)ˣ) : WeilDivisor W.X :=
  @principalWeilDivisor S W.X
    (@LocallyOfFiniteType.isLocallyNoetherian S W.X B (W.ι ≫ f)
      (locallyOfFiniteType_closedSubspace_comp W f) inferInstance) inferInstance φ

/-- The principal divisor of a rational unit is the Weil divisor
`principalWeilDivisor`. -/
theorem principalDivisor_eq (W : ClosedSubspace X) [IsIntegral W.X]
    (φ : (RationalFunction W.X)ˣ) :
    principalDivisor f W φ =
      @principalWeilDivisor S W.X
        (@LocallyOfFiniteType.isLocallyNoetherian S W.X B (W.ι ≫ f)
          (locallyOfFiniteType_closedSubspace_comp W f) inferInstance) inferInstance φ := sorry

variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (k : ℤ)

/-- The cycle obtained by pushing a principal divisor along a closed-subspace inclusion. -/
noncomputable def principalCycle (W : ClosedSubspace X) [IsIntegral W.X]
    (φ : (RationalFunction W.X)ˣ) : Function.locallyFinsupp (Points X) ℤ :=
  @Hom.closedImmersionCyclePushforward S W.X X W.ι W.isClosedImmersion
    (WeilDivisor.toCycle (principalDivisor f W φ))

/-- The pushed principal divisor of a subspace of dimension `k + 1` has degree `k`. -/
private theorem principalCycle_mem (W : ClosedSubspace X) [IsIntegral W.X]
    (hWdim : deltaDimension f δ (ClosedSubspace.irreducibleClosed W) = k + 1)
    (φ : (RationalFunction W.X)ˣ) : principalCycle f W φ ∈ cycleGroup f δ k := sorry

/-- The degree-`k` principal cycle on a closed subspace of dimension `k + 1`. -/
noncomputable def principal (W : ClosedSubspace X) [IsIntegral W.X]
    (hWdim : deltaDimension f δ (ClosedSubspace.irreducibleClosed W) = k + 1)
    (φ : (RationalFunction W.X)ˣ) : cycleGroup f δ k :=
  ⟨principalCycle f W φ, by exact principalCycle_mem f δ k W hWdim φ⟩

/-- A principal cycle is the closed-immersion pushforward of the Weil-divisor
cycle of its rational unit. -/
theorem principal_eq_pushforward_div (W : ClosedSubspace X) [IsIntegral W.X]
    (hWdim : deltaDimension f δ (ClosedSubspace.irreducibleClosed W) = k + 1)
    (φ : (RationalFunction W.X)ˣ) :
    (principal f δ k W hWdim φ : Function.locallyFinsupp (Points X) ℤ) =
      @Hom.closedImmersionCyclePushforward S W.X X W.ι W.isClosedImmersion
        (WeilDivisor.toCycle (principalDivisor f W φ)) := sorry

/-- A principal cycle lies in `Z_k(X)`. -/
theorem principal_mem_cycleGroup (W : ClosedSubspace X) [IsIntegral W.X]
    (hWdim : deltaDimension f δ (ClosedSubspace.irreducibleClosed W) = k + 1)
    (φ : (RationalFunction W.X)ˣ) :
    (principal f δ k W hWdim φ : Function.locallyFinsupp (Points X) ℤ) ∈
      cycleGroup f δ k := sorry

/-- The `j`-th principal cycle of a family of rational units on integral closed
subspaces of δ-dimension `k + 1`. -/
noncomputable def principalAt {J : Type v} (W : J → ClosedSubspace X)
    (hWint : ∀ j, IsIntegral (W j).X)
    (hWdim : ∀ j, deltaDimension f δ
      (@ClosedSubspace.irreducibleClosed S X (W j) (hWint j)) = k + 1)
    (φ : ∀ j, (RationalFunction (W j).X)ˣ) (j : J) : cycleGroup f δ k :=
  @principal S B X inferInstance inferInstance f inferInstance inferInstance
    δ inferInstance k (W j) (hWint j) (hWdim j) (φ j)

/-- Principal cycles attached to a locally finite family of integral closed
subspaces have locally finite supports. -/
theorem locallyFinite_principal_support {J : Type v} (W : J → ClosedSubspace X)
    (hWint : ∀ j, IsIntegral (W j).X)
    (hWdim : ∀ j, deltaDimension f δ
      (@ClosedSubspace.irreducibleClosed S X (W j) (hWint j)) = k + 1)
    (φ : ∀ j, (RationalFunction (W j).X)ˣ)
    (hlocal : LocallyFinite fun j ↦ (W j).pointsSet) :
    LocallyFinite fun j ↦
      (principalAt f δ k W hWint hWdim φ j :
        Function.locallyFinsupp (Points X) ℤ).support := sorry

/-- The locally finite sum of a family of principal cycles is a `k`-cycle. -/
theorem boundary_mem_cycleGroup {J : Type v} (W : J → ClosedSubspace X)
    (hWint : ∀ j, IsIntegral (W j).X)
    (hWdim : ∀ j, deltaDimension f δ
      (@ClosedSubspace.irreducibleClosed S X (W j) (hWint j)) = k + 1)
    (φ : ∀ j, (RationalFunction (W j).X)ˣ)
    (hlocal : LocallyFinite fun j ↦ (W j).pointsSet) :
    AlgebraicCycle.locallyFiniteSum
        (fun j ↦
          (principalAt f δ k W hWint hWdim φ j :
            Function.locallyFinsupp (Points X) ℤ))
        (locallyFinite_principal_support f δ k W hWint hWdim φ hlocal) ∈
      cycleGroup f δ k := sorry

/-- The `k`-cycle `∑ (i_j)_* div(φ_j)` associated to a locally finite family of
integral closed subspaces of δ-dimension `k + 1` and rational units. -/
noncomputable def boundary {J : Type v} (W : J → ClosedSubspace X)
    (hWint : ∀ j, IsIntegral (W j).X)
    (hWdim : ∀ j, deltaDimension f δ
      (@ClosedSubspace.irreducibleClosed S X (W j) (hWint j)) = k + 1)
    (φ : ∀ j, (RationalFunction (W j).X)ˣ)
    (hlocal : LocallyFinite fun j ↦ (W j).pointsSet) : cycleGroup f δ k :=
  ⟨AlgebraicCycle.locallyFiniteSum
      (fun j ↦
        (principalAt f δ k W hWint hWdim φ j :
          Function.locallyFinsupp (Points X) ℤ))
      (locallyFinite_principal_support f δ k W hWint hWdim φ hlocal),
    boundary_mem_cycleGroup f δ k W hWint hWdim φ hlocal⟩

/-- A boundary coefficient is the pointwise finite sum of the corresponding
principal-cycle coefficients. -/
theorem boundary_apply {J : Type v} (W : J → ClosedSubspace X)
    (hWint : ∀ j, IsIntegral (W j).X)
    (hWdim : ∀ j, deltaDimension f δ
      (@ClosedSubspace.irreducibleClosed S X (W j) (hWint j)) = k + 1)
    (φ : ∀ j, (RationalFunction (W j).X)ˣ)
    (hlocal : LocallyFinite fun j ↦ (W j).pointsSet) (x : Points X) :
    (boundary f δ k W hWint hWdim φ hlocal :
        Function.locallyFinsupp (Points X) ℤ) x =
      ∑ᶠ j, (principalAt f δ k W hWint hWdim φ j :
        Function.locallyFinsupp (Points X) ℤ) x := sorry

/-- Local finiteness of the supports `|W_j|` implies that the coproduct of the
inclusions `W_j ⟶ X` is proper. -/
theorem coproduct_inclusions_proper {J : Type v} [Small.{u} J]
    (W : J → ClosedSubspace X)
    (hlocal : LocallyFinite fun j ↦ (W j).pointsSet) :
    Proper (coproductDesc fun j ↦ (W j).ι) := sorry

/-- A degree-`k` cycle is rationally equivalent to zero when it is a locally
finite sum of pushforwards of principal divisors from integral closed subspaces
of δ-dimension `k + 1`. -/
def IsRationallyTrivial (α : cycleGroup f δ k) : Prop :=
  ∃ (J : Type (u + 1)) (W : J → ClosedSubspace X)
      (hWint : ∀ j, IsIntegral (W j).X)
      (hWdim : ∀ j, deltaDimension f δ
        (@ClosedSubspace.irreducibleClosed S X (W j) (hWint j)) = k + 1)
      (φ : ∀ j, (RationalFunction (W j).X)ˣ)
      (hlocal : LocallyFinite fun j ↦ (W j).pointsSet),
    α = boundary f δ k W hWint hWdim φ hlocal

/-- Rational triviality is equivalent to admitting an explicit locally finite
boundary presentation. -/
theorem isRationallyTrivial_iff_exists_boundary (α : cycleGroup f δ k) :
    IsRationallyTrivial f δ k α ↔
      ∃ (J : Type (u + 1)) (W : J → ClosedSubspace X)
          (hWint : ∀ j, IsIntegral (W j).X)
          (hWdim : ∀ j, deltaDimension f δ
            (@ClosedSubspace.irreducibleClosed S X (W j) (hWint j)) = k + 1)
          (φ : ∀ j, (RationalFunction (W j).X)ˣ)
          (hlocal : LocallyFinite fun j ↦ (W j).pointsSet),
        α = boundary f δ k W hWint hWdim φ hlocal := sorry

/-- The zero cycle is rationally equivalent to zero. -/
theorem zero_isRationallyTrivial :
    IsRationallyTrivial f δ k (0 : cycleGroup f δ k) := sorry

/-- A sum of rationally trivial cycles is rationally trivial. -/
theorem add_isRationallyTrivial {α β : cycleGroup f δ k}
    (hα : IsRationallyTrivial f δ k α) (hβ : IsRationallyTrivial f δ k β) :
    IsRationallyTrivial f δ k (α + β) := sorry

/-- The negative of a rationally trivial cycle is rationally trivial. -/
theorem neg_isRationallyTrivial {α : cycleGroup f δ k}
    (hα : IsRationallyTrivial f δ k α) :
    IsRationallyTrivial f δ k (-α) := sorry

/-- The additive subgroup of rationally trivial degree-`k` cycles. -/
def boundaries : AddSubgroup (cycleGroup f δ k) where
  carrier := {α | IsRationallyTrivial f δ k α}
  zero_mem' := zero_isRationallyTrivial f δ k
  add_mem' := add_isRationallyTrivial f δ k
  neg_mem' := neg_isRationallyTrivial f δ k

/-- Membership in the boundary subgroup is rational triviality. -/
theorem mem_boundaries_iff (α : cycleGroup f δ k) :
    α ∈ boundaries f δ k ↔ IsRationallyTrivial f δ k α := sorry

/-- Two degree-`k` cycles are rationally equivalent when their difference is
rationally equivalent to zero. -/
def RationallyEquivalent (α β : cycleGroup f δ k) : Prop :=
  α - β ∈ boundaries f δ k

/-- Rational equivalence is membership of the difference in the boundary
subgroup. -/
theorem rationallyEquivalent_iff_sub_mem (α β : cycleGroup f δ k) :
    RationallyEquivalent f δ k α β ↔ α - β ∈ boundaries f δ k := sorry

end RationalEquivalence

end AlgebraicGeometry.AlgebraicSpace

