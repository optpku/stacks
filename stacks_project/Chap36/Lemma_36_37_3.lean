/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Resolution
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 36.37.3: every derived morphism between bounded finite locally free complexes on a
quasi-compact, quasi-separated scheme with the resolution property is represented by a roof
whose middle complex is again bounded finite locally free. -/
@[stacks 0F8G] #check
  (AlgebraicGeometry.Scheme.exists_boundedFiniteLocallyFree_roof :
    {X : Scheme.{u}} → [CompactSpace X] → [QuasiSeparatedSpace X] →
      HasResolutionProperty X →
      (E F : CochainComplex X.toRingedSpace.Modules ℤ) →
      SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree.{u, u, u} E →
      SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree.{u, u, u} F →
      (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) →
      ∃ (G : CochainComplex X.toRingedSpace.Modules ℤ) (q : G ⟶ E) (g : G ⟶ F)
        (_ : SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree.{u, u, u} G) (_ : QuasiIso q),
        DerivedCategory.Q.map q ≫ α = DerivedCategory.Q.map g)

end AlgebraicGeometry.Scheme
