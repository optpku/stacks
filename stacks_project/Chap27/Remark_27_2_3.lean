module

public import ReasLib.AlgebraicGeometry.Scheme.Gluing.Basis.QuasiCoherent.Morphisms
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

/- Remark 27.2.3: compatible local morphisms of relative scheme gluing data induce a global
morphism over the base whose canonical restrictions are the prescribed local morphisms. -/
@[stacks 01LK] #check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.existsRealizationMap :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D E : AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, v} S)
      (indexEquiv : D.ι ≃ E.ι)
      (localMap : ∀ i : D.ι, D.X i ⟶ E.X (indexEquiv i))
      (compatible :
        AlgebraicGeometry.Scheme.BasisSchemeGluing.IsMorphismCompatible
          D E indexEquiv localMap)
      (R : D.Realization) (R' : E.Realization),
      ∃ globalMap : R.Y ⟶ R'.Y,
        AlgebraicGeometry.Scheme.BasisSchemeGluing.IsRealizationMap
          D E indexEquiv localMap compatible R R' globalMap)

/- Compatible local pullback-linear module maps likewise induce a global pullback-module map
whose canonical restrictions are the prescribed local module maps. -/
#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.existsRealizationMap :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D E : AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)
      (indexEquiv : D.ι ≃ E.ι)
      (localSchemeMap : ∀ i : D.ι, D.X i ⟶ E.X (indexEquiv i))
      (localModuleMap : ∀ i : D.ι,
        (AlgebraicGeometry.Scheme.Modules.pullback (localSchemeMap i)).obj
            (E.F (indexEquiv i)) ⟶
          D.F i)
      (compatible :
        AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.IsMorphismCompatible
          D E indexEquiv localSchemeMap localModuleMap)
      (R : D.Realization) (R' : E.Realization),
      ∃ (globalMap : R.Y ⟶ R'.Y)
        (globalModuleMap :
          (AlgebraicGeometry.Scheme.Modules.pullback globalMap).obj R'.M ⟶ R.M),
        AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.IsRealizationMap
          D E indexEquiv localSchemeMap localModuleMap compatible R R' globalMap
            globalModuleMap)

#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, v} :
    AlgebraicGeometry.Scheme.{u} → Type (max (u + 1) (v + 1)))

#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.Realizes :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (_D : AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, v} S)
      {X : AlgebraicGeometry.Scheme.{u}} (_f : X ⟶ S),
      Prop)

#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.Realization.nonempty :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D : AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, v} S),
      Nonempty D.Realization)

#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.Realization.existsUniqueIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D : AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, v} S)
      (R R' : D.Realization),
      ∃ e : D.RealizationIso R R', ∀ e' : D.RealizationIso R R', e' = e)

#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.{u, v} :
    AlgebraicGeometry.Scheme.{u} → Type (max (u + 1) (v + 1)))

#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.RealizesWithModule :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (_D : AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)
      {X : AlgebraicGeometry.Scheme.{u}} (_f : X ⟶ S)
      (_M : AlgebraicGeometry.Scheme.Modules X),
      Prop)

#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.Realization.realizesWithModule :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D : AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)
      (R : D.Realization),
      D.RealizesWithModule R.toBase R.M)

#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.Realization.nonempty :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D : AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S),
      Nonempty D.Realization)

#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.Realization.existsUniqueIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D : AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)
      (R R' : D.Realization),
      ∃ e : D.RealizationIso R R', ∀ e' : D.RealizationIso R R', e' = e)

#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.IsMorphismCompatible :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D E : AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, v} S)
      (indexEquiv : D.ι ≃ E.ι)
      (_localMap : ∀ i : D.ι, D.X i ⟶ E.X (indexEquiv i)),
      Prop)

#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.restrictedMap :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D E : AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, v} S)
      (indexEquiv : D.ι ≃ E.ι)
      (localMap : ∀ i : D.ι, D.X i ⟶ E.X (indexEquiv i))
      (_compatible : D.IsMorphismCompatible E indexEquiv localMap)
      (R : D.Realization) (R' : E.Realization) (globalMap : R.Y ⟶ R'.Y)
      (_overBase : globalMap ≫ R'.toBase = R.toBase) (i : D.ι),
      AlgebraicGeometry.Scheme.Opens.toScheme
          ((TopologicalSpace.Opens.map R.toBase.base).obj (D.U i)) ⟶
        AlgebraicGeometry.Scheme.Opens.toScheme
          ((TopologicalSpace.Opens.map R'.toBase.base).obj (E.U (indexEquiv i))))

#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.restrictedMap_ι :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D E : AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, v} S)
      (indexEquiv : D.ι ≃ E.ι)
      (localMap : ∀ i : D.ι, D.X i ⟶ E.X (indexEquiv i))
      (compatible : D.IsMorphismCompatible E indexEquiv localMap)
      (R : D.Realization) (R' : E.Realization) (globalMap : R.Y ⟶ R'.Y)
      (overBase : globalMap ≫ R'.toBase = R.toBase) (i : D.ι),
      D.restrictedMap E indexEquiv localMap compatible R R' globalMap overBase i ≫
          AlgebraicGeometry.Scheme.Opens.ι
            ((TopologicalSpace.Opens.map R'.toBase.base).obj (E.U (indexEquiv i))) =
        AlgebraicGeometry.Scheme.Opens.ι
            ((TopologicalSpace.Opens.map R.toBase.base).obj (D.U i)) ≫
          globalMap)

#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.IsRealizationMap :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D E : AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, v} S)
      (indexEquiv : D.ι ≃ E.ι)
      (localMap : ∀ i : D.ι, D.X i ⟶ E.X (indexEquiv i))
      (_compatible : D.IsMorphismCompatible E indexEquiv localMap)
      (R : D.Realization) (R' : E.Realization) (_globalMap : R.Y ⟶ R'.Y),
      Prop)

#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.IsMorphismCompatible :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D E : AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)
      (indexEquiv : D.ι ≃ E.ι)
      (localSchemeMap : ∀ i : D.ι, D.X i ⟶ E.X (indexEquiv i))
      (_localModuleMap : ∀ i : D.ι,
        (AlgebraicGeometry.Scheme.Modules.pullback (localSchemeMap i)).obj
            (E.F (indexEquiv i)) ⟶
          D.F i),
      Prop)

#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.restrictedModuleMap :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D E : AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)
      (indexEquiv : D.ι ≃ E.ι)
      (localSchemeMap : ∀ i : D.ι, D.X i ⟶ E.X (indexEquiv i))
      (schemeCompatible : D.toBasisSchemeGluing.IsMorphismCompatible
        E.toBasisSchemeGluing indexEquiv localSchemeMap)
      (R : D.Realization) (R' : E.Realization) (globalMap : R.Y ⟶ R'.Y)
      (overBase : globalMap ≫ R'.toBase = R.toBase)
      (_localSchemeAgreement : ∀ i : D.ι,
        (R.localSchemeIso i).hom ≫ localSchemeMap i =
          D.toBasisSchemeGluing.restrictedMap E.toBasisSchemeGluing indexEquiv localSchemeMap
              schemeCompatible R.toSchemeRealization R'.toSchemeRealization globalMap overBase
                i ≫
            (R'.localSchemeIso (indexEquiv i)).hom)
      (_globalModuleMap :
        (AlgebraicGeometry.Scheme.Modules.pullback globalMap).obj R'.M ⟶ R.M)
      (i : D.ι),
      (AlgebraicGeometry.Scheme.Modules.pullback (localSchemeMap i)).obj
          (E.F (indexEquiv i)) ⟶
        D.F i)

#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.IsRealizationMap :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D E : AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)
      (indexEquiv : D.ι ≃ E.ι)
      (localSchemeMap : ∀ i : D.ι, D.X i ⟶ E.X (indexEquiv i))
      (localModuleMap : ∀ i : D.ι,
        (AlgebraicGeometry.Scheme.Modules.pullback (localSchemeMap i)).obj
            (E.F (indexEquiv i)) ⟶
          D.F i)
      (_compatible : D.IsMorphismCompatible E indexEquiv localSchemeMap localModuleMap)
      (R : D.Realization) (R' : E.Realization) (globalMap : R.Y ⟶ R'.Y)
      (_globalModuleMap :
        (AlgebraicGeometry.Scheme.Modules.pullback globalMap).obj R'.M ⟶ R.M),
      Prop)
