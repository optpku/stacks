/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.BaseChange.InternalHom.TorIndependence
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure
open RingedSpace.ModuleDerived RingedSite.Hom Scheme.Hom

noncomputable section

universe u

/- Lemma 36.22.6 (1): in a Tor-independent cartesian square of qcqs schemes over
`Spec B ⟶ Spec A`, derived internal-Hom base change is invertible when the source is perfect
and the target has quasicoherent cohomology. -/
@[stacks 0AA7] #check
  (AlgebraicGeometry.Scheme.TorIndependentBaseChange.InternalHom.map_isIso_of_isPerfect :
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
      [IsIso (RingedSpace.modulePullbackDerived.compComparison
        f'.toShHom (Spec.map φ).toShHom)]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison
        g'.toShHom f.toShHom)]
      (sq : IsPullback g' f' f (Spec.map φ))
      (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk (Spec.map φ)))
      (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
      (M : RingedSpace.ModuleDerived X.toRingedSpace)
      (K : Scheme.ModuleDerived.Quasicoherent X)
      (hM : RingedSpace.ModuleDerived.IsPerfect M),
      IsIso (DerivedBaseChange.InternalHom.map
        sq.toCommSq H_X H_X' M K.obj))

/- Lemma 36.22.6 (2): in a Tor-independent cartesian square of qcqs schemes over
`Spec B ⟶ Spec A`, derived internal-Hom base change is invertible for a pseudo-coherent source
and a bounded-below target with quasicoherent cohomology when `B` has finite Tor dimension over
`A`. -/
@[stacks 0AA7] #check
  (AlgebraicGeometry.Scheme.TorIndependentBaseChange.InternalHom.map_isIso_of_isPseudoCoherent :
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
      [IsIso (RingedSpace.modulePullbackDerived.compComparison
        f'.toShHom (Spec.map φ).toShHom)]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison
        g'.toShHom f.toShHom)]
      (sq : IsPullback g' f' f (Spec.map φ))
      (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk (Spec.map φ)))
      (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
      (M : RingedSpace.ModuleDerived X.toRingedSpace)
      (K : Scheme.ModuleDerived.Quasicoherent X)
      (hM : RingedSpace.ModuleDerived.IsPseudoCoherent M)
      (hK : (t.plus : ObjectProperty
        (RingedSpace.ModuleDerived X.toRingedSpace)) K.obj)
      (hφ : φ.hom.HasFiniteTorDimension),
      IsIso (DerivedBaseChange.InternalHom.map
        sq.toCommSq H_X H_X' M K.obj))
