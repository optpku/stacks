/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Relative.BaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open RingedSite.Hom

noncomputable section

universe u

/- Lemma 48.28.6 -/
@[stacks 0E2Y]
#check (AlgebraicGeometry.Scheme.RelativeDualizingComplex.baseChange :
  ∀ {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (sq : IsPullback g' f' f g)
    [Flat f] [LocallyOfFinitePresentation f]
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
    (sq₂ : CommSq w (W'.ι ≫ pullback.snd f' f') (W.ι ≫ pullback.snd f f) g'),
      let hFlat : Flat f' :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance
      let hFinitePresentation : LocallyOfFinitePresentation f' :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance
      -- Local instance justification (proof-local temporary data): supplies the inverse used only to construct canonical ξ' in this theorem.
      letI : IsIso (AlgebraicGeometry.Scheme.RelativeDualizingComplex.baseChangeSource g' δ' δ w sqδ) :=
        AlgebraicGeometry.Scheme.RelativeDualizingComplex.baseChangeSource_isIso
          g' f' f g sq W δ hδ W' δ' hδ' w sqδ sq₁ sq₂
      let ξ' :=
        inv (AlgebraicGeometry.Scheme.RelativeDualizingComplex.baseChangeSource g' δ' δ w sqδ) ≫
          (RingedSpace.modulePullbackDerived w.toShHom).map C.map ≫
          (AlgebraicGeometry.Scheme.RelativeDualizingComplex.baseChangeTargetIso g' w (W'.ι ≫ pullback.fst f' f')
            (W.ι ≫ pullback.fst f f) sq₁ C.complex).hom
      @AlgebraicGeometry.Scheme.ModuleDerived.IsPerfectRelativeTo X' S' f' hFlat hFinitePresentation
          ((RingedSpace.modulePullbackDerived g'.toShHom).obj C.complex) ∧
        IsIso (AlgebraicGeometry.Scheme.RelativeDualizingComplex.dualityMap δ' H' ξ'))
