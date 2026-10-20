/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.BaseChange.InternalHom
public import ReasLib.CategoryTheory.Monoidal.Adjunction.InternalHom

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalClosed
open RingedSpace.ModuleDerived RingedSite.Hom Scheme.Hom
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.DerivedBaseChange.InternalHom

variable {X X' S S' : Scheme.{u}}
variable (g' : X' ⟶ X) {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
variable [KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [KFlat.TensorDescends X.toRingedSpace]
variable [KFlat.IsLocalization X.toRingedSpace]
variable [KFlat.HomotopyTensorDescends X'.toRingedSpace]
variable [KFlat.TensorDescends X'.toRingedSpace]
variable [KFlat.IsLocalization X'.toRingedSpace]
variable [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]
variable [DerivedAdjunction.HasPair (RingedSpace.opensRingedSiteHom g'.toShHom)]

/-- Transposing the canonical internal-Hom comparison isomorphism gives the
pullback/internal-Hom comparison followed by internal Hom applied to the derived
pullback-pushforward counit. -/
theorem adjunctionComparison_transpose
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (L : RingedSpace.ModuleDerived X'.toRingedSpace) :
    ((RingedSpace.modulePullbackDerivedPushforwardAdjunction g'.toShHom).homEquiv _ _).symm
        (CategoryTheory.Adjunction.InternalHom.comparisonIso
          (RingedSpace.modulePullbackDerivedPushforwardAdjunction g'.toShHom)
          H_X H_X' (Functor.TensorComparison.ofMonoidal (L(g'.toShHom)^*)) M L).hom =
      Functor.PullbackInternalHom.comparisonOf H_X H_X'
          (L(g'.toShHom)^*)
          (fun A B ↦ (Functor.Monoidal.μIso (L(g'.toShHom)^*) A B).symm)
          M ((R(g'.toShHom)_*).obj L) ≫
        (H_X'.ihomOf ((L(g'.toShHom)^*).obj M)).map
          ((RingedSpace.modulePullbackDerivedPushforwardAdjunction
            g'.toShHom).counit.app L) := sorry

variable [DerivedAdjunction.HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
variable [DerivedAdjunction.HasPair (RingedSpace.opensRingedSiteHom f'.toShHom)]
variable [DerivedAdjunction.HasPair (RingedSpace.opensRingedSiteHom g.toShHom)]
variable [DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom (g'.toShHom ≫ f.toShHom))]
variable [DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom (f'.toShHom ≫ g.toShHom))]
variable [IsIso (RingedSpace.modulePullbackDerived.compComparison
  f'.toShHom g.toShHom)]
variable [IsIso (RingedSpace.modulePullbackDerived.compComparison
  g'.toShHom f.toShHom)]

/-- The canonical identification of the two iterated derived pushforwards associated to a
commutative square of schemes. -/
noncomputable def pushforwardIso (sq : CommSq g' f' f g) :
    R(g'.toShHom)_* ⋙ R(f.toShHom)_* ≅
      R(f'.toShHom)_* ⋙ R(g.toShHom)_* :=
  RingedSpace.moduleDerivedPushforward.Composition.iso
      g'.toShHom f.toShHom inferInstance ≪≫
    eqToIso (congrArg
      (fun h ↦ RingedSpace.moduleDerivedPushforward h)
      (sq.map (Scheme.forgetToLocallyRingedSpace ⋙
        LocallyRingedSpace.forgetToSheafedSpace)).w) ≪≫
    (RingedSpace.moduleDerivedPushforward.Composition.iso
      f'.toShHom g.toShHom inferInstance).symm

/-- The forward component of `pushforwardIso` is the two composition isomorphisms with the
commutative-square transport between them. -/
theorem pushforwardIso_hom_app (sq : CommSq g' f' f g)
    (K : RingedSpace.ModuleDerived X'.toRingedSpace) :
    (pushforwardIso g' sq).hom.app K =
      (RingedSpace.moduleDerivedPushforward.Composition.iso
          g'.toShHom f.toShHom inferInstance).hom.app K ≫
        eqToHom (congrArg
          (fun h ↦ (RingedSpace.moduleDerivedPushforward h).obj K)
          (sq.map (Scheme.forgetToLocallyRingedSpace ⋙
            LocallyRingedSpace.forgetToSheafedSpace)).w) ≫
        (RingedSpace.moduleDerivedPushforward.Composition.iso
          f'.toShHom g.toShHom inferInstance).inv.app K := sorry

/-- The global internal-Hom adjunction isomorphism, transported across the two canonical
derived-pushforward composition isomorphisms of a commutative scheme square. -/
noncomputable def globalHomAdjunctionIso (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (L : RingedSpace.ModuleDerived X'.toRingedSpace) :
    (R(f.toShHom)_*).obj ((H_X.ihomOf M).obj ((R(g'.toShHom)_*).obj L)) ≅
      (R(g.toShHom)_*).obj
        ((R(f'.toShHom)_*).obj
          ((H_X'.ihomOf ((L(g'.toShHom)^*).obj M)).obj L)) :=
  (R(f.toShHom)_*).mapIso
      (CategoryTheory.Adjunction.InternalHom.comparisonIso
        (RingedSpace.modulePullbackDerivedPushforwardAdjunction g'.toShHom)
        H_X H_X' (Functor.TensorComparison.ofMonoidal (L(g'.toShHom)^*)) M L) ≪≫
    (pushforwardIso g' sq).app
      ((H_X'.ihomOf ((L(g'.toShHom)^*).obj M)).obj L)

/-- The forward map of `globalHomAdjunctionIso` is pushforward of the internal-Hom
comparison followed by the pushforward-composition transport. -/
theorem globalHomAdjunctionIso_hom (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (L : RingedSpace.ModuleDerived X'.toRingedSpace) :
    (globalHomAdjunctionIso g' sq H_X H_X' M L).hom =
      (R(f.toShHom)_*).map
          (CategoryTheory.Adjunction.InternalHom.comparisonIso
            (RingedSpace.modulePullbackDerivedPushforwardAdjunction g'.toShHom)
            H_X H_X' (Functor.TensorComparison.ofMonoidal (L(g'.toShHom)^*)) M L).hom ≫
        (pushforwardIso g' sq).hom.app
          ((H_X'.ihomOf ((L(g'.toShHom)^*).obj M)).obj L) := sorry

/-- The right edge obtained by applying internal Hom to the counit
`L(g')^* R(g')_* L ⟶ L` and then applying derived pushforward along `f'`. -/
noncomputable def adjunctionCounitMap (f' : X' ⟶ S')
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (L : RingedSpace.ModuleDerived X'.toRingedSpace) :
    (R(f'.toShHom)_*).obj
        ((H_X'.ihomOf ((L(g'.toShHom)^*).obj M)).obj
          ((L(g'.toShHom)^*).obj ((R(g'.toShHom)_*).obj L))) ⟶
      (R(f'.toShHom)_*).obj
        ((H_X'.ihomOf ((L(g'.toShHom)^*).obj M)).obj L) :=
  (R(f'.toShHom)_*).map
    ((H_X'.ihomOf ((L(g'.toShHom)^*).obj M)).map
      ((RingedSpace.modulePullbackDerivedPushforwardAdjunction
        g'.toShHom).counit.app L))

/-- The counit edge is derived pushforward of internal Hom applied to the
pullback-pushforward counit. -/
theorem adjunctionCounitMap_spec
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (L : RingedSpace.ModuleDerived X'.toRingedSpace) :
    adjunctionCounitMap g' f' H_X' M L =
      (R(f'.toShHom)_*).map
        ((H_X'.ihomOf ((L(g'.toShHom)^*).obj M)).map
          ((RingedSpace.modulePullbackDerivedPushforwardAdjunction
            g'.toShHom).counit.app L)) := sorry

/-- Multiplication on global derived Hom first uses the global internal-Hom adjunction
isomorphism and then applies the counit `L(g)^* R(g)_* K' ⟶ K'`. -/
noncomputable def multiplication (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (L : RingedSpace.ModuleDerived X'.toRingedSpace) :
    (RingedSpace.Hom.DerivedBaseChange.source f.toShHom g.toShHom).obj
        ((H_X.ihomOf M).obj ((R(g'.toShHom)_*).obj L)) ⟶
      (R(f'.toShHom)_*).obj
        ((H_X'.ihomOf ((L(g'.toShHom)^*).obj M)).obj L) :=
  (L(g.toShHom)^*).map (globalHomAdjunctionIso g' sq H_X H_X' M L).hom ≫
    (RingedSpace.modulePullbackDerivedPushforwardAdjunction
      g.toShHom).counit.app _

/-- Multiplication factors through pullback of the global internal-Hom adjunction isomorphism
and ends in the canonical derived pullback-pushforward counit. -/
theorem multiplication_spec (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (L : RingedSpace.ModuleDerived X'.toRingedSpace) :
    multiplication g' sq H_X H_X' M L =
      (L(g.toShHom)^*).map (globalHomAdjunctionIso g' sq H_X H_X' M L).hom ≫
        (RingedSpace.modulePullbackDerivedPushforwardAdjunction
          g.toShHom).counit.app _ := sorry

end AlgebraicGeometry.Scheme.Hom.DerivedBaseChange.InternalHom

namespace AlgebraicGeometry.Scheme.TorIndependentBaseChange.InternalHom

/-- For an affine Tor-independent cartesian square of quasi-compact, quasi-separated schemes,
the derived internal-Hom base-change map commutes with multiplication and the morphism induced
by the pullback-pushforward counit. -/
theorem map_counit_commSq {A B : CommRingCat.{u}} (φ : A ⟶ B)
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
    (L : RingedSpace.ModuleDerived X'.toRingedSpace) :
    CommSq
      (Hom.DerivedBaseChange.InternalHom.map
        sq.toCommSq H_X H_X' M ((R(g'.toShHom)_*).obj L))
      (Hom.DerivedBaseChange.InternalHom.multiplication
        g' sq.toCommSq H_X H_X' M L)
      (Hom.DerivedBaseChange.InternalHom.adjunctionCounitMap
        g' f' H_X' M L)
      (𝟙 _) := sorry

end AlgebraicGeometry.Scheme.TorIndependentBaseChange.InternalHom
