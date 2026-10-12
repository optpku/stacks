/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.BaseChange.Comparison.ScalarExtension
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.ProjectionFormula
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finiteness criteria for scalar-extension RHom base change

@stack 0A6A

This leaf records the four source criteria under which the canonical
scalar-extension comparison for `RHom` is invertible.  The comparison morphism
itself remains owned by `RHom.BaseChange.ScalarExtension.comparisonApp`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.ScalarExtension

variable {R S : Type u} [CommRing R] [CommRing S]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} R))]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} S))]
variable [RHom.Has (A := R)] [RHom.Has (A := S)]

/-- Lemma 15.100.2 (1) (0A6A): scalar-extension `RHom` base change is an
isomorphism when the source object is perfect. -/
@[stacks 0A6A "Lemma 15.100.2 (1): perfect source"]
theorem comparisonApp_isIso_of_source_isPerfect
    (σ : R →+* S)
    (MR : RHom.BifunctorComparison (A := R))
    (MS : RHom.BifunctorComparison (A := S))
    (T : TensorComparison σ)
    (K L : DerivedCategory (ModuleCat.{u} R))
    (hK : K.IsPerfect) :
    IsIso (comparisonApp σ MR MS T K L) := sorry

/-- Lemma 15.100.2 (2) (0A6A): scalar-extension `RHom` base change is an
isomorphism when the target ring is perfect as a source-ring module. -/
@[stacks 0A6A "Lemma 15.100.2 (2): perfect target ring"]
theorem comparisonApp_isIso_of_targetRing_isPerfect
    (σ : R →+* S)
    (MR : RHom.BifunctorComparison (A := R))
    (MS : RHom.BifunctorComparison (A := S))
    (T : TensorComparison σ)
    (K L : DerivedCategory (ModuleCat.{u} R))
    (hS : (ModuleCat.restrictedRegular₀ σ).IsPerfect) :
    IsIso (comparisonApp σ MR MS T K L) := sorry

/-- Lemma 15.100.2 (3) (0A6A): flat scalar extension preserves the `RHom`
comparison for a pseudo-coherent source and bounded-below target. -/
@[stacks 0A6A "Lemma 15.100.2 (3): flat pseudo-coherent case"]
theorem comparisonApp_isIso_of_flat_of_isPseudoCoherent_of_boundedBelow
    (σ : R →+* S)
    (MR : RHom.BifunctorComparison (A := R))
    (MS : RHom.BifunctorComparison (A := S))
    (T : TensorComparison σ)
    (K L : DerivedCategory (ModuleCat.{u} R))
    (hσ : σ.Flat) (hK : K.IsPseudoCoherent)
    (hL : ∃ n : ℤ, L.IsGE n) :
    IsIso (comparisonApp σ MR MS T K L) := sorry

/-- Lemma 15.100.2 (4) (0A6A): finite Tor dimension of the target ring gives
the `RHom` comparison for a pseudo-coherent source and bounded-below target. -/
@[stacks 0A6A "Lemma 15.100.2 (4): finite-Tor pseudo-coherent case"]
theorem comparisonApp_isIso_of_finiteTorDimension_of_isPseudoCoherent_of_boundedBelow
    (σ : R →+* S)
    (MR : RHom.BifunctorComparison (A := R))
    (MS : RHom.BifunctorComparison (A := S))
    (T : TensorComparison σ)
    (K L : DerivedCategory (ModuleCat.{u} R))
    (hS : HasFiniteTorDimension (R := R) (ModuleCat.restrictedRegular₀ σ))
    (hK : K.IsPseudoCoherent) (hL : ∃ n : ℤ, L.IsGE n) :
    IsIso (comparisonApp σ MR MS T K L) := sorry

/-- Lemma 15.100.2 (0A6A): the scalar-extension comparison is invertible in
any of the four standard finiteness cases. -/
@[stacks 0A6A "Lemma 15.100.2 scalar-extension RHom criterion"]
theorem comparisonApp_isIso_of_finiteness
    (σ : R →+* S)
    (MR : RHom.BifunctorComparison (A := R))
    (MS : RHom.BifunctorComparison (A := S))
    (T : TensorComparison σ)
    (K L : DerivedCategory (ModuleCat.{u} R))
    (hcases : K.IsPerfect ∨ (ModuleCat.restrictedRegular₀ σ).IsPerfect ∨
      (σ.Flat ∧ K.IsPseudoCoherent ∧ ∃ n : ℤ, L.IsGE n) ∨
      (HasFiniteTorDimension (R := R) (ModuleCat.restrictedRegular₀ σ) ∧
        K.IsPseudoCoherent ∧ ∃ n : ℤ, L.IsGE n)) :
    IsIso (comparisonApp σ MR MS T K L) := by
  rcases hcases with hK | hS | ⟨hσ, hK, hL⟩ | ⟨hS, hK, hL⟩
  · exact comparisonApp_isIso_of_source_isPerfect σ MR MS T K L hK
  · exact comparisonApp_isIso_of_targetRing_isPerfect σ MR MS T K L hS
  · exact
      comparisonApp_isIso_of_flat_of_isPseudoCoherent_of_boundedBelow
        σ MR MS T K L hσ hK hL
  · exact
      comparisonApp_isIso_of_finiteTorDimension_of_isPseudoCoherent_of_boundedBelow
        σ MR MS T K L hS hK hL

end CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.ScalarExtension
