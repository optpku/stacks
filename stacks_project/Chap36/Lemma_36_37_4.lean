/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Resolution
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 36.37.4: two maps between bounded finite locally free complexes that agree in the
derived category become homotopic after precomposition with a quasi-isomorphism from another
bounded finite locally free complex. -/
@[stacks 0F8H] #check
  (AlgebraicGeometry.Scheme.exists_homotopy_refinement_of_derived_eq :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (hX : HasResolutionProperty X)
      (E F : CochainComplex X.toRingedSpace.Modules ℤ)
      (hE : SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree.{u, u, u} E)
      (hF : SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree.{u, u, u} F)
      (α β : E ⟶ F) (hαβ : DerivedCategory.Q.map α = DerivedCategory.Q.map β),
      ∃ (G : CochainComplex X.toRingedSpace.Modules ℤ) (γ : G ⟶ E),
        SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree.{u, u, u} G ∧
          QuasiIso γ ∧ Nonempty (Homotopy (γ ≫ α) (γ ≫ β)))

end AlgebraicGeometry.Scheme
