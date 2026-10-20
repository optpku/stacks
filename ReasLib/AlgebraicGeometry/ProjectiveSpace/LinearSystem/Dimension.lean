module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearSystem
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic

/-!
# Dimension bounds for generating linear systems

This file records dimension bounds for subspaces that retain the generating property of a
linear system.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem

/-- Over an infinite field, a generating linear system on an algebraic scheme restricts to a
finite-dimensional generating subspace whose rank is at most the normalized Krull dimension
plus one. -/
theorem exists_generatingSubmodule_finrank_le_topologicalKrullDim_add_one
    {k : Type u} [Field k] [Infinite k]
    (X : Over (Spec (CommRingCat.of k))) [Algebraic X]
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    {V : Type u} [AddCommGroup V] [Module k V]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    ∃ W : Submodule k V,
      FiniteDimensional k W ∧
        (Module.finrank k W : ℕ∞) ≤ (topologicalKrullDim X.left + 1).unbotD 0 ∧
          Generates X L (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype ≫ ψ) := sorry

end AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem
