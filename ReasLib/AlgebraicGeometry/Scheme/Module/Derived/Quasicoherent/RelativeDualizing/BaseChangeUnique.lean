module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizing.ProperFlat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Relative.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Relative.Uniqueness

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open CategoryTheory.MonoidalCategory
open RingedSite.Hom

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.RelativeDualizingComplex

/-- For a proper flat finitely presented morphism, a relative dualizing complex
and its base-change data determine a unique compatible isomorphism after any
quasi-compact quasi-separated base change. -/
theorem baseChangeExistsUniqueIso
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (sq : IsPullback g' f' f g)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    [CompactSpace S'] [QuasiSeparatedSpace S']
    (W : (pullback f f).Opens) (δ : X ⟶ W.toScheme) [IsClosedImmersion δ]
    (hδ : δ ≫ W.ι = pullback.diagonal f)
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal]
    (H : MonoidalClosed (RingedSpace.ModuleDerived W.toScheme.toRingedSpace))
    (C : Scheme.RelativeDualizingComplex f W δ hδ H)
    (W' : (pullback f' f').Opens) (δ' : X' ⟶ W'.toScheme) [IsClosedImmersion δ']
    (hδ' : δ' ≫ W'.ι = pullback.diagonal f')
    [HomotopyTensorDescends X'.toRingedSpace]
    [TensorDescends X'.toRingedSpace]
    [IsLocalization X'.toRingedSpace]
    [MonoidalCategory (RingedSpace.ModuleDerived W'.toScheme.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ'.toShHom).LaxMonoidal]
    (H' : MonoidalClosed (RingedSpace.ModuleDerived W'.toScheme.toRingedSpace))
    (w : W'.toScheme ⟶ W.toScheme)
    [DerivedAdjunction.HasPair (RingedSpace.opensRingedSiteHom δ.toShHom)]
    [DerivedAdjunction.HasPair (RingedSpace.opensRingedSiteHom δ'.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived g'.toShHom)]
    (sqδ : IsPullback g' δ' δ w)
    (sq₁ : CommSq w (W'.ι ≫ pullback.fst f' f') (W.ι ≫ pullback.fst f f) g')
    (sq₂ : CommSq w (W'.ι ≫ pullback.snd f' f') (W.ι ≫ pullback.snd f f) g')
    (hTor : Scheme.TorIndependentOver (Over.mk δ) (Over.mk w))
    (ξ' : (diagonalAlgebra δ').X ⟶
      (RingedSpace.modulePullbackDerived
        (W'.ι ≫ pullback.fst f' f').toShHom).obj
          ((RingedSpace.modulePullbackDerived g'.toShHom).obj C.complex))
    (hξ : CommSq
      ((RingedSpace.modulePullbackDerived w.toShHom).map C.map)
      (baseChangeSource g' δ' δ w sqδ)
      (baseChangeTargetIso g' w (W'.ι ≫ pullback.fst f' f')
        (W.ι ≫ pullback.fst f f) sq₁ C.complex).hom ξ') :
    let hQuasiCompact : QuasiCompact f' :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance
    let hQuasiSeparated : QuasiSeparated f' :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance
    ∀ (a' : DerivedQCoh S' ⥤ DerivedQCoh X')
      (f'Adjunction : @DerivedQCoh.pushforwardCohomologyIn X' S' f'
        hQuasiCompact hQuasiSeparated ⊣ a')
      (c' : DerivedQCoh W'.toScheme ⥤ DerivedQCoh X')
      (c'Adjunction : DerivedQCoh.pushforwardCohomologyIn δ' ⊣ c')
      (e' : DerivedQCoh.structureSheaf X' ≅
        c'.obj ((DerivedQCoh.pullback
          (W'.ι ≫ pullback.fst f' f')).obj
            (@DerivedQCoh.relativeDualizingComplex X' S' f'
              hQuasiCompact hQuasiSeparated a' f'Adjunction))),
      ∃! e :
          (@DerivedQCoh.relativeDualizingComplex X' S' f'
            hQuasiCompact hQuasiSeparated a' f'Adjunction).obj ≅
            (RingedSpace.modulePullbackDerived g'.toShHom).obj C.complex,
        mapOfAdjointIso δ' c' c'Adjunction
              ((DerivedQCoh.pullback
                (W'.ι ≫ pullback.fst f' f')).obj
                  (@DerivedQCoh.relativeDualizingComplex X' S' f'
                    hQuasiCompact hQuasiSeparated a' f'Adjunction)) e' ≫
            (DerivedQCoh.pullback.inclusionIso
              (W'.ι ≫ pullback.fst f' f')).hom.app
                (@DerivedQCoh.relativeDualizingComplex X' S' f'
                  hQuasiCompact hQuasiSeparated a' f'Adjunction) ≫
            (RingedSpace.modulePullbackDerived
              (W'.ι ≫ pullback.fst f' f').toShHom).map e.hom = ξ' := sorry

end AlgebraicGeometry.Scheme.RelativeDualizingComplex
