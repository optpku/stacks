/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CardinalGeneration

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Cardinal CategoryTheory.Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- Pullback preserves cardinal-bounded local generation. -/
theorem pullback_isKappaGenerated {X Y : Scheme.{u}} (f : X ⟶ Y)
    {κ : Cardinal.{u}} {F : Y.QCoh} (hF : F.obj.IsKappaGenerated κ) :
    ((pullback f).obj F).obj.IsKappaGenerated κ := sorry

end AlgebraicGeometry.Scheme.QCoh
