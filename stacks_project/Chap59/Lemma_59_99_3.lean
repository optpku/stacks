module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Derived.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open AlgebraicGeometry.StandardTopology.Big
open RingedSite.Hom.ModuleSections.Underlying

noncomputable section

universe u

/- Lemma 59.99.3 (1): ordinary derived cohomology on the big étale site over `S` agrees with
the cohomology of the identity inverse image on the small étale site. -/
@[stacks 0DDH] #check
  (AlgebraicGeometry.Scheme.Etale.Derived.etaleCohomology_piInverseImage :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
      [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
      [IsGrothendieckAbelian
        (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
      [IsGrothendieckAbelian
        (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
      [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
      [PreservesFiniteLimits
        ((relocalizationFunctor (𝟙 S)).op.lan :
          (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
            ((Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}))]
      (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})),
      IsIsomorphic
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
          ((siteAbelianSectionsDerived (S.overGrothendieckTopology @Etale)
            (Over.mk (𝟙 S))).obj
              ((siteAbelianPullbackDerived S.smallEtaleTopology
                (S.overGrothendieckTopology @Etale) (relocalizationFunctor (𝟙 S))).obj K)))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
          ((siteAbelianSectionsDerived S.smallEtaleTopology
            (terminal S.Etale)).obj K)))

/- Lemma 59.99.3 (2): module-valued derived cohomology on the big étale site agrees with the
cohomology of the identity pullback on the small étale site. -/
@[stacks 0DDH] #check
  (AlgebraicGeometry.Scheme.Etale.Module.Derived.etaleModuleCohomology_piPullback :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
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
        (Small.ringedSite S)),
      IsIsomorphic
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
          ((sectionsDerived.{u + 1}
            (StandardTopology.Big.ringedSite .etale S) (Over.mk (𝟙 S))).obj
            ((RingedSite.Hom.modulePullbackDerived.{u + 1}
              (Scheme.SiteRestriction.bigToEtale .etale S
                AlgebraicGeometry.Scheme.etale_ne_zariski)).obj K)))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
          ((sectionsDerived.{u + 1}
            (Small.ringedSite S) (terminal S.Etale)).obj K)))

/- Lemma 59.99.3 (3): ordinary derived cohomology on `T` agrees with small-site cohomology after
the inverse image associated to `f : T ⟶ S`. -/
@[stacks 0DDH] #check
  (AlgebraicGeometry.Scheme.Etale.Derived.etaleCohomology_smallInverseImage :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
      [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
      [IsGrothendieckAbelian
        (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
      [IsGrothendieckAbelian
        (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
      [IsGrothendieckAbelian
        (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
      [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
      [PreservesFiniteLimits
        ((relocalizationFunctor (𝟙 S)).op.lan :
          (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
            ((Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}))]
      [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (smallEtalePullback f).op.HasLeftKanExtension P]
      [PreservesFiniteLimits
        ((smallEtalePullback f).op.lan :
          (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
            (T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}))]
      (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})),
      IsIsomorphic
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
          ((siteAbelianSectionsDerived (S.overGrothendieckTopology @Etale)
            (Over.mk f)).obj
              ((siteAbelianPullbackDerived S.smallEtaleTopology
                (S.overGrothendieckTopology @Etale) (relocalizationFunctor (𝟙 S))).obj K)))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
          ((siteAbelianSectionsDerived T.smallEtaleTopology
            (terminal T.Etale)).obj
              ((siteAbelianPullbackDerived S.smallEtaleTopology
                T.smallEtaleTopology (smallEtalePullback f)).obj K))))

/- Lemma 59.99.3 (4): module-valued derived cohomology on `T` agrees with small-site cohomology
after the derived pullback associated to `f : T ⟶ S`. -/
@[stacks 0DDH] #check
  (AlgebraicGeometry.Scheme.Etale.Module.Derived.etaleModuleCohomology_smallPullback :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
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
        (Small.ringedSite S)),
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
              (Small.ringedHom f)).obj K))))

/- Lemma 59.99.3 (5): ordinary derived cohomology on the big site over `S` agrees with cohomology
on the small étale site of `T` after relocalization. -/
@[stacks 0DDH] #check
  (AlgebraicGeometry.Scheme.Etale.Derived.etaleCohomology_relocalization :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
      [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
      [IsGrothendieckAbelian
        (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
      [IsGrothendieckAbelian
        (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
      (M : DerivedCategory
        (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})),
      IsIsomorphic
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
          ((siteAbelianSectionsDerived (S.overGrothendieckTopology @Etale)
            (Over.mk f)).obj M))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
          ((siteAbelianSectionsDerived T.smallEtaleTopology
            (terminal T.Etale)).obj
            ((siteAbelianInverseImageDerived T.smallEtaleTopology
              (S.overGrothendieckTopology @Etale)
              (relocalizationFunctor f)).obj M))))

/- Lemma 59.99.3 (6): module-valued derived cohomology on the big site over `S` agrees with
cohomology on the small étale site of `T` after relocalization. -/
@[stacks 0DDH] #check
  (AlgebraicGeometry.Scheme.Etale.Module.Derived.etaleModuleCohomology_relocalization :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
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
        (liftedRingedSite .etale S)),
      IsIsomorphic
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
          ((sectionsDerived.{u + 1}
            (liftedRingedSite .etale S) (Over.mk f)).obj M))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
          ((sectionsDerived.{u + 1}
            (Small.liftedRingedSite T) (terminal T.Etale)).obj
            ((RingedSite.ToposHom.modulePullbackDerived.{u + 1}
              (ringedToposHom f)).obj M))))

end

end
