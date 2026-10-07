module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Restriction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.ModuleDerived
open AlgebraicGeometry.Scheme.Modules.IdealPowerComplex
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

universe v

/- Remark 48.31.3
For nested open immersions `i : U' ⟶ U` and `j : U ⟶ X` of Noetherian schemes, the
extension-by-zero object on `U'` admits a unique restriction morphism to the
extension-by-zero object on `U`, characterized by the compact-support restriction predicate. -/
@[stacks 0G4Y] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.existsUnique_extensionByZeroRestriction :
    ∀ {X U U' : Scheme.{v}} (i : U' ⟶ U) (j : U ⟶ X)
      [IsNoetherian X] [IsNoetherian U] [IsNoetherian U']
      [IsOpenImmersion i] [IsOpenImmersion j]
      (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
      (K' : Dᵇ[SheafOfModules.isCoherent U'.ringCatSheaf])
      (restrictionIso : K' ≅
        (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.restriction i).obj K),
      ∃! f :
          (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.extensionByZero
            (i ≫ j)).obj K' ⟶
            (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.extensionByZero j).obj K,
        AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.IsExtensionByZeroRestriction
          i j K K' restrictionIso f)

#check
  (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.extensionByZeroRestriction_naturality :
    ∀ {X U U' : Scheme.{v}} (i : U' ⟶ U) (j : U ⟶ X)
      [IsNoetherian X] [IsNoetherian U] [IsNoetherian U']
      [IsOpenImmersion i] [IsOpenImmersion j]
      {K L : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]}
      {K' L' : Dᵇ[SheafOfModules.isCoherent U'.ringCatSheaf]}
      (restrictionIsoK : K' ≅
        (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.restriction i).obj K)
      (restrictionIsoL : L' ≅
        (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.restriction i).obj L)
      (f : K ⟶ L) (f' : K' ⟶ L')
      (_ : f' ≫ restrictionIsoL.hom = restrictionIsoK.hom ≫
        (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.restriction i).map f)
      (rK :
        (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.extensionByZero
          (i ≫ j)).obj K' ⟶
          (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.extensionByZero j).obj K)
      (rL :
        (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.extensionByZero
          (i ≫ j)).obj L' ⟶
          (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.extensionByZero j).obj L)
      (_ : AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.IsExtensionByZeroRestriction
        i j K K' restrictionIsoK rK)
      (_ : AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.IsExtensionByZeroRestriction
        i j L L' restrictionIsoL rL),
      (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.extensionByZero (i ≫ j)).map f' ≫ rL =
        rK ≫ (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.extensionByZero j).map f)

#check
  (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.idealPowerCompactSupportMap_isRestriction :
    ∀ {X U U' : Scheme.{v}} (i : U' ⟶ U) (j : U ⟶ X)
      [IsNoetherian X] [IsNoetherian U] [IsNoetherian U']
      [IsOpenImmersion i] [IsOpenImmersion j]
      (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
      (K' : Dᵇ[SheafOfModules.isCoherent U'.ringCatSheaf])
      (restrictionIso : K' ≅
        (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.restriction i).obj K)
      (I I' : X.IdealSheafData)
      (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf))
      (hU : I.openComplement = j.opensRange)
      (hU' : I'.openComplement = (i ≫ j).opensRange)
      (h : I' ≤ I)
      (systemIso :
        positiveDerivedSystem I F.obj ⋙ RingedSpace.modulePullbackDerived j.toShHom ≅
          (Functor.const (OrderDual ℕ+)).obj
            ((ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj K))
      (systemIso' :
        positiveDerivedSystem I' F.obj ⋙
            RingedSpace.modulePullbackDerived (i ≫ j).toShHom ≅
          (Functor.const (OrderDual ℕ+)).obj
            ((ambient (SheafOfModules.isCoherent U'.ringCatSheaf)).obj K'))
      (sourceIso :
        AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.boundedProObject (i ≫ j)
            (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.ofIdealPower
              (i ≫ j) I' F hU' K' systemIso') ≅
          (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.extensionByZero
            (i ≫ j)).obj K')
      (targetIso :
        AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.boundedProObject j
            (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.ofIdealPower
              j I F hU K systemIso) ≅
          (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.extensionByZero j).obj K)
      (_ :
        AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.CompatibleIdealPowerPresentations
          i j K K' restrictionIso I I' F hU hU' h systemIso systemIso'
            sourceIso targetIso),
      AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.IsExtensionByZeroRestriction
        i j K K' restrictionIso
        (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.idealPowerCompactSupportMap
          i j K K' I I' F hU hU' h systemIso systemIso' sourceIso targetIso))
