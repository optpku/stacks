/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import ReasLib.RingTheory.Flatness.LocallyFree
import Mathlib.Tactic.CrossRefAttribute

/-!
# Norms of finite locally free morphisms

This file owns the canonical finite-morphism norm for a finite locally free morphism of constant
rank.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (π : X ⟶ Y) (d : ℕ)

/-- The section rings over affine opens of a finite locally free morphism of constant rank `d`
are finite locally free of rank `d`. -/
theorem finiteLocallyFreeOfRank_on_affineOpens [IsFiniteLocallyFreeOfRank π d]
    (U : Y.Opens) (hU : IsAffineOpen U) :
    Module.FiniteLocallyFreeOfRank (Γ(Y, U)) (Γ(X, π ⁻¹ᵁ U)) d := sorry

namespace FiniteMorphismNorm

variable {π : X ⟶ Y}

/-- A finite-morphism norm is determinantal when, after every scalar extension on which the
source section algebra is finite free, its value is the determinant of multiplication. -/
def IsDeterminant (N : FiniteMorphismNorm π) : Prop :=
  ∀ (U : Y.Opens) (hU : IsAffineOpen U)
      (S : Type*) [CommRing S] [Algebra (Γ(Y, U)) S]
      [Module.Free S (S ⊗[Γ(Y, U)] Γ(X, π ⁻¹ᵁ U))]
      [Module.Finite S (S ⊗[Γ(Y, U)] Γ(X, π ⁻¹ᵁ U))]
      (x : S ⊗[Γ(Y, U)] Γ(X, π ⁻¹ᵁ U)),
    N.baseChange U hU S x = Algebra.norm S x

end FiniteMorphismNorm

/-- A finite locally free morphism of constant positive rank admits a norm satisfying the power
and zero-locus conditions, universally characterized by determinants after scalar extension. -/
@[stacks 0BD2]
theorem exists_norm_of_finiteLocallyFreeOfRank [IsFiniteLocallyFreeOfRank π d] (hd : 1 ≤ d) :
    ∃ N : FiniteMorphismNorm π, IsFiniteMorphismNorm π d N ∧ N.IsDeterminant := sorry

end AlgebraicGeometry.Scheme
