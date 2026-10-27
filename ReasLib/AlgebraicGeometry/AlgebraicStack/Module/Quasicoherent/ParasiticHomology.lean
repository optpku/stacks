/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Homology
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Abelian
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Parasitic

/-! # Exactness of quasi-coherent complexes and parasitic homology -/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

/-- A short complex of quasi-coherent modules on an algebraic stack is exact if
and only if its homology computed in étale or fppf modules is parasitic. -/
theorem exact_iff_homology_isParasitic
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (sc : ShortComplex (QCoh X)) {τ : StandardTopology}
    (hτ : τ = .etale ∨ τ = .fppf) :
    sc.Exact ↔ IsParasitic (associatedModulePresheaf (associatedHomology X τ sc)) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
