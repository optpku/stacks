/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Topological consequences of finite presentation

A finite-presentation morphism transfers quasi-compactness and quasi-separatedness from its
target scheme to its source scheme.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The source of a finite-presentation morphism with quasi-compact target is quasi-compact. -/
theorem compactSpace_of_finitePresentation [CompactSpace S] [FinitePresentation f] :
    CompactSpace X :=
  QuasiCompact.compactSpace_of_compactSpace f

/-- The source of a finite-presentation morphism with quasi-separated target is
quasi-separated. -/
theorem quasiSeparatedSpace_of_finitePresentation [QuasiSeparatedSpace S]
    [FinitePresentation f] : QuasiSeparatedSpace X :=
  quasiSeparatedSpace_of_quasiSeparated f

/-- The source of a finite-presentation morphism with quasi-compact and quasi-separated target
is quasi-compact and quasi-separated. -/
theorem compactSpace_and_quasiSeparatedSpace_of_finitePresentation [CompactSpace S]
    [QuasiSeparatedSpace S] [FinitePresentation f] :
    CompactSpace X ∧ QuasiSeparatedSpace X :=
  ⟨compactSpace_of_finitePresentation f, quasiSeparatedSpace_of_finitePresentation f⟩

end AlgebraicGeometry.Scheme.Hom
