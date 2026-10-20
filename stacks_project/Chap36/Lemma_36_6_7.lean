/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.Derived
public import stacks_project.Chap36.Remark_36_6_6

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 36.6.7: for a quasi-coherent module sheaf, the derived principal-open
extended Čech complex represents the local-cohomology object supported on the
common zero locus of the chosen global sections. -/
@[stacks 0G7M]
#check (ModuleCech.ofSectionsToLocalCohomology_isIso :
  ∀ {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent],
    IsIso ((ModuleCech.ofSectionsToLocalCohomology f).app ℱ))

end
