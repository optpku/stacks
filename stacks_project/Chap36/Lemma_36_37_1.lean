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

/- Lemma 36.37.1: on a quasi-compact and quasi-separated scheme with the resolution property,
every bounded-below termwise quasi-coherent complex representing a perfect derived object admits
a quasi-isomorphism from a bounded complex of finite locally free modules. -/
@[stacks 0F8E] #check
  (AlgebraicGeometry.Scheme.exists_boundedFiniteLocallyFree_quasiIso :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (hX : AlgebraicGeometry.Scheme.HasResolutionProperty X)
      (F : CochainComplex X.toRingedSpace.Modules ℤ)
      (hF_boundedBelow : CochainComplex.plus X.toRingedSpace.Modules F)
      (hF_quasicoherent : ∀ n : ℤ,
        AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace (F.X n))
      (hF_perfect : AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect
        (DerivedCategory.Q.obj F)),
      ∃ (E : CochainComplex X.toRingedSpace.Modules ℤ) (α : E ⟶ F),
        SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree E ∧ QuasiIso α)
