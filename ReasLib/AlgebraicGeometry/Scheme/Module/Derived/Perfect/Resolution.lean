/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.LocallyFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.ResolutionProperty
import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Bounded
import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Characterization
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Cohomology
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison.AffineDiagonal
import ReasLib.AlgebraicGeometry.Scheme.Module.ResolutionProperty.AffineDiagonal

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- On a quasi-compact and quasi-separated scheme with the resolution property, every
bounded-below termwise quasi-coherent complex representing a perfect derived object admits a
quasi-isomorphism from a bounded complex of finite locally free modules. -/
theorem exists_boundedFiniteLocallyFree_quasiIso {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (hX : HasResolutionProperty X)
    (F : CochainComplex X.toRingedSpace.Modules ℤ)
    (hF_boundedBelow : CochainComplex.plus X.toRingedSpace.Modules F)
    (hF_quasicoherent : ∀ n : ℤ,
      RingedSpace.quasiCoherentModuleProperty X.toRingedSpace (F.X n))
    (hF_perfect : RingedSpace.ModuleDerived.IsPerfect (DerivedCategory.Q.obj F)) :
    ∃ (E : CochainComplex X.toRingedSpace.Modules ℤ) (α : E ⟶ F),
      SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree.{u, u, u} E ∧ QuasiIso α := sorry

/-- On a quasi-compact and quasi-separated scheme with the resolution property, every perfect
derived module is represented by a bounded complex of finite locally free modules. -/
theorem exists_boundedFiniteLocallyFree_representative {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (hX : HasResolutionProperty X)
    (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (hK : RingedSpace.ModuleDerived.IsPerfect K) :
    ∃ E : CochainComplex X.toRingedSpace.Modules ℤ,
      ∃ _ : K ≅ DerivedCategory.Q.obj E,
        SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree.{u, u, u} E := sorry

/-- On a quasi-compact and quasi-separated scheme with the resolution property, every derived
morphism between bounded complexes of finite locally free modules is represented by a roof whose
middle complex is bounded finite locally free and whose left leg is a quasi-isomorphism. -/
theorem exists_boundedFiniteLocallyFree_roof {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (hX : HasResolutionProperty X)
    (E F : CochainComplex X.toRingedSpace.Modules ℤ)
    (hE : SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree.{u, u, u} E)
    (hF : SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree.{u, u, u} F)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) :
    ∃ (G : CochainComplex X.toRingedSpace.Modules ℤ) (q : G ⟶ E) (g : G ⟶ F)
      (hG : SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree.{u, u, u} G) (hq : QuasiIso q),
      DerivedCategory.Q.map q ≫ α = DerivedCategory.Q.map g := sorry

/-- Two maps between bounded finite locally free complexes that agree in the derived category
become homotopic after precomposition with a quasi-isomorphism from another bounded finite
locally free complex. -/
theorem exists_homotopy_refinement_of_derived_eq {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (hX : HasResolutionProperty X)
    (E F : CochainComplex X.toRingedSpace.Modules ℤ)
    (hE : SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree.{u, u, u} E)
    (hF : SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree.{u, u, u} F)
    (α β : E ⟶ F) (hαβ : DerivedCategory.Q.map α = DerivedCategory.Q.map β) :
    ∃ (G : CochainComplex X.toRingedSpace.Modules ℤ) (γ : G ⟶ E),
      SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree.{u, u, u} G ∧
        QuasiIso γ ∧ Nonempty (Homotopy (γ ≫ α) (γ ≫ β)) := sorry

end AlgebraicGeometry.Scheme
