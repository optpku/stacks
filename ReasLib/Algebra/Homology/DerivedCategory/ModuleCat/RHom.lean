/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom
public import Mathlib.Algebra.Category.ModuleCat.AB

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace ModuleCat

/-- The same-universe module category admits the canonical unbounded derived `RHom`. -/
instance hasDerivedHom (A : Type u) [CommRing A] :
    CategoryTheory.CochainComplex.Enriched.Over.RHom.Has
      (R := A) (C := ModuleCat.{u} A) := by
  exact CategoryTheory.CochainComplex.Enriched.Over.RHom.hasRightDerivedFunctor
    (R := A) (C := ModuleCat.{u} A)

end ModuleCat
