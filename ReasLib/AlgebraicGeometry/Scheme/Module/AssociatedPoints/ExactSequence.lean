/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk
public import ReasLib.RingTheory.Ideal.AssociatedPrime.ExactSequence
public import ReasLib.Topology.Sheaves.Abelian.Sheafification

/-!
# Associated Points in Exact Sequences

This module relates the associated points of the terms in a short exact complex of
quasi-coherent modules on a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {S : ShortComplex X.Modules}

/-- In a short exact complex of quasi-coherent modules on a scheme, every associated point of
the middle term belongs to the associated-point set of one of the outer terms. -/
theorem associatedPoints_middle_subset_union_of_shortExact
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (hS : S.ShortExact) :
    associatedPoints S.X₂ ⊆ associatedPoints S.X₁ ∪ associatedPoints S.X₃ := sorry

/-- In a short exact complex of quasi-coherent modules on a scheme, every associated point of
the left term is an associated point of the middle term. -/
theorem associatedPoints_left_subset_of_shortExact
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (hS : S.ShortExact) :
    associatedPoints S.X₁ ⊆ associatedPoints S.X₂ := by
  intro x hx
  rw [mem_associatedPoints_iff] at hx ⊢
  exact associatedPrimesOfModule.subset_of_injective
    (RingedSpace.moduleStalkShortComplex_shortExact S x hS).moduleCat_injective_f hx

end AlgebraicGeometry.Scheme.Modules
