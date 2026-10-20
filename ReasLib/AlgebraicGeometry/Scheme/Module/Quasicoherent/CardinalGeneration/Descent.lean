/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CardinalGeneration

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Cardinal

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.QCoh

/-- Cardinal-bounded local generation descends along fpqc covering families. -/
theorem of_fpqcCovering {X : Scheme.{u}} {ι : Type v} {κ : Cardinal.{u}}
    (F : X.Modules) [F.IsQuasicoherent] (family : ι → Over X)
    (hfamily : Scheme.FpqcCovering family)
    (hpullback : ∀ i, ((Modules.pullback (family i).hom).obj F).IsKappaGenerated κ) :
    F.IsKappaGenerated κ := sorry

end AlgebraicGeometry.Scheme.QCoh
