module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.BaseChange.Affine
public import stacks_project.Chap36.Lemma_36_4_1
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory DerivedCategory.Plus.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

open BaseChange

/- Lemma 48.6.2 (1): for a Tor-independent cartesian square of quasi-compact,
quasi-separated schemes with `Y` and `Y'` affine and `f` proper, flat, and of finite
presentation, the right-adjoint base-change map is an isomorphism on every
`K : DerivedQCoh Y`. -/
@[stacks 0AA8] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.mapOfRight_app_isIso_of_flat :
    ∀ {X' X Y' Y : Scheme.{u}}
      [CompactSpace X'] [QuasiSeparatedSpace X']
      [CompactSpace X] [QuasiSeparatedSpace X]
      [IsAffine Y'] [IsAffine Y]
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
      [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
      (sq : IsPullback g' f' f g)
      (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g))
      (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
      (fAdj : pushforwardCohomologyIn f ⊣ a)
      (f'Adj : pushforwardCohomologyIn f' ⊣ a')
      (dualBaseChangeIso :
        a' ⋙ pushforwardCohomologyIn g' ≅ pushforwardCohomologyIn g ⋙ a)
      (h_dualBaseChange : dualBaseChangeIso.hom =
        rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj)
      (K : DerivedQCoh Y),
      IsIso
        ((DerivedBaseChange.mapOfRight
          (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction g')
          dualBaseChangeIso.inv).app K))

/- Lemma 48.6.2 (2): for a Tor-independent cartesian square of quasi-compact,
quasi-separated schemes with `Y` and `Y'` affine, `f` proper and perfect, and `Y`
Noetherian, the right-adjoint base-change map is an isomorphism on every
`K : DerivedQCoh Y`. -/
@[stacks 0AA8] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.mapOfRight_app_isIso_of_perfect :
    ∀ {X' X Y' Y : Scheme.{u}}
      [CompactSpace X'] [QuasiSeparatedSpace X']
      [CompactSpace X] [QuasiSeparatedSpace X]
      [IsAffine Y'] [IsAffine Y] [IsNoetherian Y]
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
      [IsProper f] [LocallyOfType RingHom.IsPerfectRingMap f]
      (sq : IsPullback g' f' f g)
      (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g))
      (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
      (fAdj : pushforwardCohomologyIn f ⊣ a)
      (f'Adj : pushforwardCohomologyIn f' ⊣ a')
      (dualBaseChangeIso :
        a' ⋙ pushforwardCohomologyIn g' ≅ pushforwardCohomologyIn g ⋙ a)
      (h_dualBaseChange : dualBaseChangeIso.hom =
        rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj)
      (K : DerivedQCoh Y),
      IsIso
        ((DerivedBaseChange.mapOfRight
          (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction g')
          dualBaseChangeIso.inv).app K))

/- Lemma 48.6.2 (3): for a Tor-independent cartesian square of quasi-compact,
quasi-separated schemes with `Y` and `Y'` affine, `f` proper, `g` of finite Tor
dimension, and `Y` Noetherian, the right-adjoint base-change map is an isomorphism on
every `K : DerivedQCoh.Plus Y`. -/
@[stacks 0AA8] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.mapOfRight_app_isIso_of_finiteTorDimension :
    ∀ {X' X Y' Y : Scheme.{u}}
      [CompactSpace X'] [QuasiSeparatedSpace X']
      [CompactSpace X] [QuasiSeparatedSpace X]
      [IsAffine Y'] [IsAffine Y] [IsNoetherian Y]
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
      [IsProper f] [RingedSpace.Hom.HasFiniteTorDimension g.toShHom]
      (sq : IsPullback g' f' f g)
      (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g))
      (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
      (fAdj : pushforwardCohomologyIn f ⊣ a)
      (f'Adj : pushforwardCohomologyIn f' ⊣ a')
      (dualBaseChangeIso :
        a' ⋙ pushforwardCohomologyIn g' ≅ pushforwardCohomologyIn g ⋙ a)
      (h_dualBaseChange : dualBaseChangeIso.hom =
        rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj)
      (K : DerivedQCoh.Plus Y),
      IsIso
        ((DerivedBaseChange.mapOfRight
          (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction g')
          dualBaseChangeIso.inv).app
            ((toUnbounded Y.toRingedSpace.quasiCoherentModuleProperty).obj K)))

end AlgebraicGeometry.Scheme.DerivedQCoh
