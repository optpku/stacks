module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Ext.Functor
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Single

/-! # Restriction and precomposition of module-valued Ext classes -/

@[expose] public section

open CategoryTheory
open DerivedCategory HomologicalComplex ComplexShape

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.Ext

/-- The Ext map `Res_A(Ext^i_B(E_y, N)) ⟶ Ext^i_A(E_x, Res_A N)` induced by
restriction of scalars and a functoriality map `E_x ⟶ Res_A(E_y)`. -/
def restrictionMap {A B : Type u} [CommRing A] [CommRing B] {σ : A →+* B}
    {Kx : DerivedCategory (ModuleCat.{u} A)} {Ky : DerivedCategory (ModuleCat.{u} B)}
    (f : Kx ⟶ (ModuleCat.derivedRestrictionOfScalars σ).obj Ky) (i : ℤ)
    (N : ModuleCat.{u} B) :
    (ModuleCat.restrictScalars.{u + 1} σ).obj
        ((DerivedCategory.Ext.moduleFunctor Ky i).obj N) ⟶
      (DerivedCategory.Ext.moduleFunctor Kx i).obj
        ((ModuleCat.restrictScalars σ).obj N) :=
  let action := fun (α : (ModuleCat.restrictScalars.{u + 1} σ).obj
      ((DerivedCategory.Ext.moduleFunctor Ky i).obj N)) ↦
      (show (DerivedCategory.Ext.moduleFunctor Kx i).obj
        ((ModuleCat.restrictScalars σ).obj N) from
        f ≫ (ModuleCat.derivedRestrictionOfScalars σ).map α ≫
          ((ModuleCat.derivedRestrictionOfScalars σ).commShiftIso i).hom.app
            ((singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj N) ≫
          ((ModuleCat.DerivedRestriction.singleIso σ (0 : ℤ) N).hom)⟦i⟧')
  have laws : (∀ a b, action (a + b) = action a + action b) ∧
      (∀ (a : A) b, action (a • b) = a • action b) := by sorry
  ConcreteCategory.ofHom
    { toFun := action
      map_add' := laws.1
      map_smul' := laws.2 }


/-- `restrictionMap` is precomposition with `E_x ⟶ Res_A(E_y)` after
transporting Ext classes along derived restriction, the shift comparison, and
`singleIso`. -/
theorem restrictionMap_apply {A B : Type u} [CommRing A] [CommRing B]
    {σ : A →+* B} {Kx : DerivedCategory (ModuleCat.{u} A)}
    {Ky : DerivedCategory (ModuleCat.{u} B)}
    (f : Kx ⟶ (ModuleCat.derivedRestrictionOfScalars σ).obj Ky) (i : ℤ)
    (N : ModuleCat.{u} B)
    (α : (ModuleCat.restrictScalars.{u + 1} σ).obj
      ((DerivedCategory.Ext.moduleFunctor Ky i).obj N)) :
    restrictionMap f i N α =
      f ≫ (ModuleCat.derivedRestrictionOfScalars σ).map α ≫
        ((ModuleCat.derivedRestrictionOfScalars σ).commShiftIso i).hom.app
          ((singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj N) ≫
        ((ModuleCat.DerivedRestriction.singleIso σ (0 : ℤ) N).hom)⟦i⟧' :=
  rfl

end CategoryTheory.DerivedCategory.Ext
