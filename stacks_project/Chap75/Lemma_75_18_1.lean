/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.HomotopyColimit
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/- Lemma 75.18.1: on a quasi-compact quasi-separated algebraic space, a derived module is
pseudo-coherent iff it admits a sequential homotopy-colimit presentation by perfect objects
whose canonical maps become isomorphisms after successively lower truncations. -/
@[stacks 0DKB] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.isPseudoCoherent_iff_exists_perfect_homotopyColimit :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (K : ModuleDerived X),
      IsPseudoCoherent X K ↔
        ∃ (Kseq : ℕ ⥤ ModuleDerived X)
          (P : HomotopyColimit.Presentation Kseq K),
          ∀ n : ℕ,
            IsPerfect (Kseq.obj n) ∧
              IsIso ((t.truncGE (-((n : ℤ) + 1))).map (P.ι n)))

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
