/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.TorIndependence.BaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open RingedSite.Hom
open AlgebraicGeometry.RingedSpace.Hom.DerivedBaseChange

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.RelativeDualizingComplex

/-- The canonical comparison from the derived pullback of the old diagonal algebra to the
new diagonal algebra in a cartesian square. -/
noncomputable def baseChangeSource
    {X' X W' W : Scheme.{u}} (g' : X' ⟶ X) (δ' : X' ⟶ W') (δ : X ⟶ W)
    (w : W' ⟶ W)
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived X'.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived W.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived W'.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal]
    [(RingedSpace.moduleDerivedPushforward δ'.toShHom).LaxMonoidal]
    [DerivedAdjunction.HasPair (RingedSpace.opensRingedSiteHom δ.toShHom)]
    [DerivedAdjunction.HasPair (RingedSpace.opensRingedSiteHom δ'.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived g'.toShHom)]
    (sq : IsPullback g' δ' δ w) :
    (RingedSpace.modulePullbackDerived w.toShHom).obj (diagonalAlgebra δ).X ⟶
      (diagonalAlgebra δ').X :=
  (@Hom.DerivedBaseChange.map _ _ _ _ g' δ' δ w _ _
      (RingedSpace.modulePullbackDerived.compComparison_isIso δ'.toShHom w.toShHom)
      (RingedSpace.modulePullbackDerived.compComparison_isIso g'.toShHom δ.toShHom)
      sq.toCommSq).app (𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace)) ≫
    (RingedSpace.moduleDerivedPushforward δ'.toShHom).map
      (Functor.Monoidal.εIso (RingedSpace.modulePullbackDerived g'.toShHom)).inv

/-- `baseChangeSource` is the derived base-change component on the tensor unit followed by
the inverse monoidal unit comparison. -/
theorem baseChangeSource_spec
    {X' X W' W : Scheme.{u}} (g' : X' ⟶ X) (δ' : X' ⟶ W') (δ : X ⟶ W)
    (w : W' ⟶ W)
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived X'.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived W.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived W'.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal]
    [(RingedSpace.moduleDerivedPushforward δ'.toShHom).LaxMonoidal]
    [DerivedAdjunction.HasPair (RingedSpace.opensRingedSiteHom δ.toShHom)]
    [DerivedAdjunction.HasPair (RingedSpace.opensRingedSiteHom δ'.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived g'.toShHom)]
    (sq : IsPullback g' δ' δ w) :
    baseChangeSource g' δ' δ w sq =
      (@Hom.DerivedBaseChange.map _ _ _ _ g' δ' δ w _ _
          (RingedSpace.modulePullbackDerived.compComparison_isIso δ'.toShHom w.toShHom)
          (RingedSpace.modulePullbackDerived.compComparison_isIso g'.toShHom δ.toShHom)
          sq.toCommSq).app (𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace)) ≫
        (RingedSpace.moduleDerivedPushforward δ'.toShHom).map
          (Functor.Monoidal.εIso (RingedSpace.modulePullbackDerived g'.toShHom)).inv := sorry

/-- The canonical isomorphism between the two iterated derived pullbacks in a cartesian square. -/
noncomputable def baseChangeTargetIso
    {X' X W' W : Scheme.{u}} (g' : X' ⟶ X) (w : W' ⟶ W)
    (p' : W' ⟶ X') (p : W ⟶ X) (sq : CommSq w p' p g')
    (K : RingedSpace.ModuleDerived X.toRingedSpace) :
    (RingedSpace.modulePullbackDerived w.toShHom).obj
        ((RingedSpace.modulePullbackDerived p.toShHom).obj K) ≅
      (RingedSpace.modulePullbackDerived p'.toShHom).obj
        ((RingedSpace.modulePullbackDerived g'.toShHom).obj K) :=
  ((@pullbackIsoOfIsIso _ _ _ _ w.toShHom p'.toShHom p.toShHom g'.toShHom
      ((sq.map (Scheme.forgetToLocallyRingedSpace ⋙
        LocallyRingedSpace.forgetToSheafedSpace)) :
          CommSq w.toShHom p'.toShHom p.toShHom g'.toShHom)
      (RingedSpace.modulePullbackDerived.compComparison_isIso p'.toShHom g'.toShHom)
      (RingedSpace.modulePullbackDerived.compComparison_isIso w.toShHom p.toShHom)).symm.app K)

/-- The forward map of `baseChangeTargetIso` is the canonical pullback comparison. -/
theorem baseChangeTargetIso_hom
    {X' X W' W : Scheme.{u}} (g' : X' ⟶ X) (w : W' ⟶ W)
    (p' : W' ⟶ X') (p : W ⟶ X) (sq : CommSq w p' p g')
    (K : RingedSpace.ModuleDerived X.toRingedSpace) :
    (baseChangeTargetIso g' w p' p sq K).hom =
      ((@pullbackIsoOfIsIso _ _ _ _ w.toShHom p'.toShHom p.toShHom g'.toShHom
        ((sq.map (Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace)) :
            CommSq w.toShHom p'.toShHom p.toShHom g'.toShHom)
        (RingedSpace.modulePullbackDerived.compComparison_isIso p'.toShHom g'.toShHom)
        (RingedSpace.modulePullbackDerived.compComparison_isIso w.toShHom p.toShHom)).symm.app K).hom := sorry

/-- Tor independence of the diagonal factor and the induced open base-change map. -/
theorem baseChangeTorIndependent
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (sq : IsPullback g' f' f g)
    [Flat f] [LocallyOfFinitePresentation f]
    (W : (pullback f f).Opens) (δ : X ⟶ W.toScheme) [IsClosedImmersion δ]
    (hδ : δ ≫ W.ι = pullback.diagonal f)
    (W' : (pullback f' f').Opens) (δ' : X' ⟶ W'.toScheme) [IsClosedImmersion δ']
    (hδ' : δ' ≫ W'.ι = pullback.diagonal f')
    (w : W'.toScheme ⟶ W.toScheme)
    (sqδ : IsPullback g' δ' δ w)
    (sq₁ : CommSq w (W'.ι ≫ pullback.fst f' f') (W.ι ≫ pullback.fst f f) g')
    (sq₂ : CommSq w (W'.ι ≫ pullback.snd f' f') (W.ι ≫ pullback.snd f f) g') :
    Scheme.TorIndependentOver (Over.mk δ) (Over.mk w) := sorry

/-- The diagonal source comparison is invertible in the flat cartesian base-change situation. -/
theorem baseChangeSource_isIso
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (sq : IsPullback g' f' f g)
    [Flat f] [LocallyOfFinitePresentation f]
    (W : (pullback f f).Opens) (δ : X ⟶ W.toScheme) [IsClosedImmersion δ]
    (hδ : δ ≫ W.ι = pullback.diagonal f)
    (W' : (pullback f' f').Opens) (δ' : X' ⟶ W'.toScheme) [IsClosedImmersion δ']
    (hδ' : δ' ≫ W'.ι = pullback.diagonal f')
    (w : W'.toScheme ⟶ W.toScheme) (sqδ : IsPullback g' δ' δ w)
    (sq₁ : CommSq w (W'.ι ≫ pullback.fst f' f') (W.ι ≫ pullback.fst f f) g')
    (sq₂ : CommSq w (W'.ι ≫ pullback.snd f' f') (W.ι ≫ pullback.snd f f) g')
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived X'.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived W'.toScheme.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal]
    [(RingedSpace.moduleDerivedPushforward δ'.toShHom).LaxMonoidal]
    [DerivedAdjunction.HasPair (RingedSpace.opensRingedSiteHom δ.toShHom)]
    [DerivedAdjunction.HasPair (RingedSpace.opensRingedSiteHom δ'.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived g'.toShHom)] :
    IsIso (baseChangeSource g' δ' δ w sqδ) := sorry

/-- A relative dualizing complex remains relative dualizing after the canonical derived base change. -/
theorem baseChange
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (sq : IsPullback g' f' f g)
    [Flat f] [LocallyOfFinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f'.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f'.toShHom).restrict U.isOpenEmbedding))]
    (W : (pullback f f).Opens) (δ : X ⟶ W.toScheme) [IsClosedImmersion δ]
    (hδ : δ ≫ W.ι = pullback.diagonal f)
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal]
    (H : MonoidalClosed (RingedSpace.ModuleDerived W.toScheme.toRingedSpace))
    (C : Scheme.RelativeDualizingComplex f W δ hδ H)
    (W' : (pullback f' f').Opens) (δ' : X' ⟶ W'.toScheme) [IsClosedImmersion δ']
    (hδ' : δ' ≫ W'.ι = pullback.diagonal f')
    [MonoidalCategory (RingedSpace.ModuleDerived X'.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived W'.toScheme.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ'.toShHom).LaxMonoidal]
    (H' : MonoidalClosed (RingedSpace.ModuleDerived W'.toScheme.toRingedSpace))
    (w : W'.toScheme ⟶ W.toScheme)
    [DerivedAdjunction.HasPair (RingedSpace.opensRingedSiteHom δ.toShHom)]
    [DerivedAdjunction.HasPair (RingedSpace.opensRingedSiteHom δ'.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived g'.toShHom)]
    (sqδ : IsPullback g' δ' δ w)
    (sq₁ : CommSq w (W'.ι ≫ pullback.fst f' f') (W.ι ≫ pullback.fst f f) g')
    (sq₂ : CommSq w (W'.ι ≫ pullback.snd f' f') (W.ι ≫ pullback.snd f f) g') :
    let hFlat : Flat f' :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance
    let hFinitePresentation : LocallyOfFinitePresentation f' :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance
    -- Local instance justification (proof-local temporary data): supplies the inverse used only to define the canonical ξ' in this theorem.
    letI : IsIso (baseChangeSource g' δ' δ w sqδ) :=
      baseChangeSource_isIso g' f' f g sq W δ hδ W' δ' hδ' w sqδ sq₁ sq₂
    let ξ' :=
      inv (baseChangeSource g' δ' δ w sqδ) ≫
        (RingedSpace.modulePullbackDerived w.toShHom).map C.map ≫
        (baseChangeTargetIso g' w (W'.ι ≫ pullback.fst f' f')
          (W.ι ≫ pullback.fst f f) sq₁ C.complex).hom
    @ModuleDerived.IsPerfectRelativeTo X' S' f' hFlat hFinitePresentation inferInstance
        ((RingedSpace.modulePullbackDerived g'.toShHom).obj C.complex) ∧
      IsIso (dualityMap δ' H' ξ') := sorry

end AlgebraicGeometry.Scheme.RelativeDualizingComplex
