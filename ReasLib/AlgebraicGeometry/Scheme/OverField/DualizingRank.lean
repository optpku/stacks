/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Topology.KrullDimension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.OverField.ExtPairing

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- If the trace pairings of a finite locally free dualizing module are nondegenerate
in every complementary degree on a nonempty proper scheme over an algebraically closed field,
then its constant rank is one. -/
theorem dualizingModule_finiteLocallyFree_rank_eq_one
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Nonempty X.left] [IsProper X.hom] [HasExt (X.left.Modules)]
    (d : ℕ) (hd : topologicalKrullDim X.left = d) (ω : X.left.Modules)
    (t : Ext (𝟙_ (X.left.Modules)) ω d →ₗ[k] k)
    (h_pair : ∀ (i : ℕ) (hi : i ≤ d) (F : X.left.Modules) [F.IsCoherent],
      (tracePairing X t F hi).Nondegenerate)
    (h_neg : ∀ (i : ℕ) (F : X.left.Modules) [F.IsCoherent],
      d < i → Subsingleton (Ext F ω i))
    (r : ℕ) [IsFiniteLocallyFreeOfRank r ω] :
    r = 1 :=
  sorry

end AlgebraicGeometry.SchemeOverField
