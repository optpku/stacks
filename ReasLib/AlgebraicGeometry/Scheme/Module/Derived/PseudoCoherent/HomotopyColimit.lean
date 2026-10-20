/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Definition

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- On a quasi-compact quasi-separated scheme, a derived module is pseudo-coherent exactly
when it has a sequential homotopy-colimit presentation by perfect objects whose canonical maps
become isomorphisms after successively lower truncations. -/
theorem isPseudoCoherent_iff_exists_perfect_homotopyColimit {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (K : RingedSpace.ModuleDerived X.toRingedSpace) :
    RingedSpace.ModuleDerived.IsPseudoCoherent K ↔
      ∃ (Kseq : ℕ ⥤ RingedSpace.ModuleDerived X.toRingedSpace)
        (P : HomotopyColimit.Presentation Kseq K),
        ∀ n : ℕ,
          RingedSpace.ModuleDerived.IsPerfect (Kseq.obj n) ∧
            IsIso ((t.truncGE (-((n : ℤ) + 1))).map (P.ι n)) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
