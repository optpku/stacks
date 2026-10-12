/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.BaseChange.InternalHom.Counit
public import stacks_project.Chap36.Lemma_36_22_6

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpace.ModuleDerived RingedSite.Hom Scheme.Hom
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

universe u

/- Remark 36.22.7: for the affine Tor-independent base-change square of
Lemma 36.22.6, the internal-Hom base-change map commutes with multiplication and the map
induced by the counit `L(g')^* R(g')_* L ⟶ L`. -/
@[stacks 0BZA] #check
  (AlgebraicGeometry.Scheme.TorIndependentBaseChange.InternalHom.map_counit_commSq :
    ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B)
      {X X' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Spec B)
      (f : X ⟶ Spec A) [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace X'] [QuasiSeparatedSpace X']
      [KFlat.HomotopyTensorDescends X.toRingedSpace]
      [KFlat.TensorDescends X.toRingedSpace]
      [KFlat.IsLocalization X.toRingedSpace]
      [KFlat.HomotopyTensorDescends X'.toRingedSpace]
      [KFlat.TensorDescends X'.toRingedSpace]
      [KFlat.IsLocalization X'.toRingedSpace]
      [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]
      [DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom f.toShHom)]
      [DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom f'.toShHom)]
      [DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom g'.toShHom)]
      [DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom (Spec.map φ).toShHom)]
      [DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom (g'.toShHom ≫ f.toShHom))]
      [DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom
          (f'.toShHom ≫ (Spec.map φ).toShHom))]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison
        f'.toShHom (Spec.map φ).toShHom)]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison
        g'.toShHom f.toShHom)]
      (sq : IsPullback g' f' f (Spec.map φ))
      (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk (Spec.map φ)))
      (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
      (M : RingedSpace.ModuleDerived X.toRingedSpace)
      (L : RingedSpace.ModuleDerived X'.toRingedSpace),
      CommSq
        (Scheme.Hom.DerivedBaseChange.InternalHom.map
          sq.toCommSq H_X H_X' M ((R(g'.toShHom)_*).obj L))
        (Scheme.Hom.DerivedBaseChange.InternalHom.multiplication
          g' sq.toCommSq H_X H_X' M L)
        (Scheme.Hom.DerivedBaseChange.InternalHom.adjunctionCounitMap
          g' f' H_X' M L)
        (𝟙 _))

section Multiplication

variable {A B : CommRingCat.{u}} (φ : A ⟶ B)
variable [DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom (Spec.map φ).toShHom)]
variable (K' : RingedSpace.ModuleDerived (Spec B).toRingedSpace)

#check
  ((RingedSpace.modulePullbackDerivedPushforwardAdjunction
      (Spec.map φ).toShHom).counit.app K' :
    (L((Spec.map φ).toShHom)^*).obj
        ((R((Spec.map φ).toShHom)_*).obj K') ⟶ K')

end Multiplication
