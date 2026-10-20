/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.RingedTopos
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Zariski
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback
public import ReasLib.CategoryTheory.Sites.Derived.Sections

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.Small
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open AlgebraicGeometry.StandardTopology.Big
open RingedSite.Hom.ModuleSections.Underlying

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale.Module.Derived

variable {S T : Scheme.{u}}

/-- Restriction of a big étale module direct image agrees with small-site direct image. -/
theorem directImageRestrict
    (f : T ⟶ S) [UnivLE.{u + 1, v}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{v}]
    [T.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{v}]
    [S.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (T.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(T.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(S.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [IsGrothendieckAbelian (SheafOfModules.{v} (Small.structureSheaf T))]
    [IsGrothendieckAbelian (SheafOfModules.{v} (Small.structureSheaf S))]
    [IsGrothendieckAbelian
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))]
    [IsGrothendieckAbelian
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S))]
    [HasDerivedCategory (SheafOfModules.{v} (Small.structureSheaf T))]
    [HasDerivedCategory (SheafOfModules.{v} (Small.structureSheaf S))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S))]
    [(Module.smallDirectImage f).Additive] [(Module.bigDirectImage f).Additive]
    (K : DerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))) :
    IsIsomorphic
      ((relocalization (𝟙 S)).obj ((bigDirectImage f).obj K))
      ((smallDirectImage f).obj ((relocalization (𝟙 T)).obj K)) := sorry

/-- Restriction commutes with direct image across an arbitrary cartesian square. -/
theorem directImageRelocalization
    {S' T' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S)
    (g' : T' ⟶ T) (f' : T' ⟶ S') (hcart : IsPullback g' f' f g)
    [UnivLE.{u + 1, v}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{v}]
    [T.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{v}]
    [S.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify T'.smallEtaleTopology AddCommGrpCat.{v}]
    [T'.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{v}]
    [S'.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (T.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(T.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(S.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (T'.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(T'.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (S'.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(S'.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [IsGrothendieckAbelian (SheafOfModules.{v} (Small.structureSheaf T'))]
    [IsGrothendieckAbelian (SheafOfModules.{v} (Small.structureSheaf S'))]
    [IsGrothendieckAbelian
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))]
    [IsGrothendieckAbelian
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S))]
    [HasDerivedCategory (SheafOfModules.{v} (Small.structureSheaf T'))]
    [HasDerivedCategory (SheafOfModules.{v} (Small.structureSheaf S'))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S))]
    [(Module.smallDirectImage f').Additive] [(Module.bigDirectImage f).Additive]
    (K : DerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))) :
    IsIsomorphic
      ((relocalization g).obj ((bigDirectImage f).obj K))
      ((smallDirectImage f').obj ((relocalization g').obj K)) := sorry

/-- Big-site inverse image commutes with direct image across a cartesian square. -/
theorem bigBaseChange
    {S' T' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S)
    (g' : T' ⟶ T) (f' : T' ⟶ S') (hcart : IsPullback g' f' f g)
    [UnivLE.{u + 1, v}]
    [HasSheafify (T.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(T.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(S.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (T'.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(T'.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (S'.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(S'.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [IsGrothendieckAbelian
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))]
    [IsGrothendieckAbelian
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S))]
    [IsGrothendieckAbelian
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T'))]
    [IsGrothendieckAbelian
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S'))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T'))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S'))]
    [(Module.bigDirectImage f).Additive] [(Module.bigDirectImage f').Additive]
    (K : DerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))) :
    IsIsomorphic
      ((bigInverseImage g).obj ((bigDirectImage f).obj K))
      ((bigDirectImage f').obj ((bigInverseImage g').obj K)) := sorry

/-- Identity-base derived module pullback identifies big and small étale cohomology. -/
theorem etaleModuleCohomology_piPullback
    {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
    [UnivLE.{u + 1, u + 1}]
    [(Scheme.SiteRestriction.bigToEtale .etale S
      AlgebraicGeometry.Scheme.etale_ne_zariski).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u + 1}
        (Scheme.SiteRestriction.bigToEtale .etale S
          AlgebraicGeometry.Scheme.etale_ne_zariski))
      (RingedSite.Hom.ModuleQis.{u + 1} (Small.ringedSite S))]
    [IsGrothendieckAbelian
      (RingedSite.ModuleCat.{u + 1} (Small.ringedSite S))]
    [IsGrothendieckAbelian
      (RingedSite.ModuleCat.{u + 1}
        (StandardTopology.Big.ringedSite .etale S))]
    (K : RingedSite.Hom.ModuleDerived.{u + 1}
      (Small.ringedSite S)) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1}
          (StandardTopology.Big.ringedSite .etale S) (Over.mk (𝟙 S))).obj
          ((RingedSite.Hom.modulePullbackDerived.{u + 1}
            (Scheme.SiteRestriction.bigToEtale .etale S
              AlgebraicGeometry.Scheme.etale_ne_zariski)).obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1}
          (Small.ringedSite S) (terminal S.Etale)).obj K)) := sorry

/-- Derived module pullback along a scheme morphism identifies big and small étale cohomology. -/
theorem etaleModuleCohomology_smallPullback
    {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
    [UnivLE.{u + 1, u + 1}]
    [(Scheme.SiteRestriction.bigToEtale .etale S
      AlgebraicGeometry.Scheme.etale_ne_zariski).modulePushforward.{u + 1}.IsRightAdjoint]
    [(Small.ringedHom f).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u + 1}
        (Scheme.SiteRestriction.bigToEtale .etale S
          AlgebraicGeometry.Scheme.etale_ne_zariski))
      (RingedSite.Hom.ModuleQis.{u + 1} (Small.ringedSite S))]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u + 1}
        (Small.ringedHom f))
      (RingedSite.Hom.ModuleQis.{u + 1} (Small.ringedSite S))]
    [IsGrothendieckAbelian
      (RingedSite.ModuleCat.{u + 1} (Small.ringedSite T))]
    [IsGrothendieckAbelian
      (RingedSite.ModuleCat.{u + 1}
        (StandardTopology.Big.ringedSite .etale S))]
    [IsGrothendieckAbelian
      (RingedSite.ModuleCat.{u + 1} (Small.ringedSite S))]
    (K : RingedSite.Hom.ModuleDerived.{u + 1}
      (Small.ringedSite S)) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1}
          (StandardTopology.Big.ringedSite .etale S) (Over.mk f)).obj
          ((RingedSite.Hom.modulePullbackDerived.{u + 1}
            (Scheme.SiteRestriction.bigToEtale .etale S
              AlgebraicGeometry.Scheme.etale_ne_zariski)).obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1}
          (Small.ringedSite T) (terminal T.Etale)).obj
          ((RingedSite.Hom.modulePullbackDerived.{u + 1}
            (Small.ringedHom f)).obj K))) := sorry

/-- Relocalization identifies derived module cohomology on the big and small étale sites. -/
theorem etaleModuleCohomology_relocalization
    {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
    [UnivLE.{u + 1, u + 1}]
    [(SheafOfModules.restrictScalars
      (ringedToposHom f).structureMap).IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.ToposHom.modulePullbackToDerived.{u + 1}
        (ringedToposHom f))
      (RingedSite.Hom.ModuleQis.{u + 1} (liftedRingedSite .etale S))]
    [IsGrothendieckAbelian
      (RingedSite.ModuleCat (Small.liftedRingedSite T))]
    [IsGrothendieckAbelian
      (RingedSite.ModuleCat (liftedRingedSite .etale S))]
    (M : RingedSite.Hom.ModuleDerived
      (liftedRingedSite .etale S)) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1}
          (liftedRingedSite .etale S) (Over.mk f)).obj M))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1}
          (Small.liftedRingedSite T) (terminal T.Etale)).obj
          ((RingedSite.ToposHom.modulePullbackDerived.{u + 1}
            (ringedToposHom f)).obj M))) := sorry

end AlgebraicGeometry.Scheme.Etale.Module.Derived

end
