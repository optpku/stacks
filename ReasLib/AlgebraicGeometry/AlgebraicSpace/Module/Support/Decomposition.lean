/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Support decompositions of coherent algebraic-space modules

A coherent module whose support is a union of two closed subsets admits a short exact
decomposition into coherent modules supported on the respective subsets.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A coherent module on a Noetherian algebraic space whose support is the union of two
closed subsets admits a short exact sequence with coherent submodule supported on the
second subset and coherent quotient supported on the first. -/
theorem exists_shortExact_of_support_eq_union
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (F : X.Modules) [F.IsCoherent]
    (Z Z' : TopologicalSpace.Closeds (Points X))
    (hSupp : moduleSupport F = (Z : Set (Points X)) ∪ (Z' : Set (Points X))) :
    ∃ (G' G : X.Modules) (hG' : SheafOfModules.IsCoherent G')
      (hG : SheafOfModules.IsCoherent G)
      (ι : G' ⟶ F) (π : F ⟶ G) (w : ι ≫ π = 0)
      (hSuppG : moduleSupport G ⊆ (Z : Set (Points X))),
      (ShortComplex.mk ι π w).ShortExact ∧
        moduleSupport G' ⊆ (Z' : Set (Points X)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
