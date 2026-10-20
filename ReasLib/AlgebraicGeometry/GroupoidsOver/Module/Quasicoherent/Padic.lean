/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import ReasLib.AlgebraicGeometry.FormalSpectrum.Padic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Presheaf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent

/-!
# Nonabelian quasi-coherent modules on the p-adic formal spectrum
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry.AffineFormalAlgebraicSpace

namespace AlgebraicGeometry.GroupoidsOver.QCoh

/-- The category of quasi-coherent modules on the groupoid fibration associated
to the p-adic formal spectrum is not abelian. -/
theorem not_abelian (p : ℕ) [Fact p.Prime] :
    ¬ Nonempty (Abelian (QCoh (GroupoidsOver.ofPresheaf (padicSpectrum p).obj))) := sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
