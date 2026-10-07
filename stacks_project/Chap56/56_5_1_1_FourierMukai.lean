module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

#check (AlgebraicGeometry.Scheme.QCoh.tensorRightPreservesQuasiCoherent :
  ∀ {P : AlgebraicGeometry.Scheme.{u}} (K : AlgebraicGeometry.Scheme.QCoh P),
    AlgebraicGeometry.Scheme.quasiCoherentModuleProperty P ≤
      (AlgebraicGeometry.Scheme.quasiCoherentModuleProperty P).inverseImage
        (CategoryTheory.MonoidalCategory.tensorRight K.obj))

#check (AlgebraicGeometry.Scheme.QCoh.tensorRight :
  ∀ {P : AlgebraicGeometry.Scheme.{u}},
    AlgebraicGeometry.Scheme.QCoh P →
      (AlgebraicGeometry.Scheme.QCoh P ⥤ AlgebraicGeometry.Scheme.QCoh P))

#check (AlgebraicGeometry.Scheme.QCoh.tensorRight_obj :
  ∀ {P : AlgebraicGeometry.Scheme.{u}}
    (K : AlgebraicGeometry.Scheme.QCoh P)
    (F : AlgebraicGeometry.Scheme.QCoh P),
    ((AlgebraicGeometry.Scheme.QCoh.tensorRight K).obj F).obj =
      (CategoryTheory.MonoidalCategory.tensorRight K.obj).obj F.obj)

#check (AlgebraicGeometry.Scheme.QCoh.fourierMukai :
  ∀ {S X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact (CategoryTheory.Limits.pullback.snd f g)]
    [QuasiSeparated (CategoryTheory.Limits.pullback.snd f g)],
    AlgebraicGeometry.Scheme.QCoh (CategoryTheory.Limits.pullback f g) →
      (AlgebraicGeometry.Scheme.QCoh X ⥤ AlgebraicGeometry.Scheme.QCoh Y))

#check (AlgebraicGeometry.Scheme.QCoh.fourierMukai_obj :
  ∀ {S X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact (CategoryTheory.Limits.pullback.snd f g)]
    [QuasiSeparated (CategoryTheory.Limits.pullback.snd f g)]
    (K : AlgebraicGeometry.Scheme.QCoh (CategoryTheory.Limits.pullback f g))
    (F : AlgebraicGeometry.Scheme.QCoh X),
    (AlgebraicGeometry.Scheme.QCoh.fourierMukai f g K).obj F =
      (AlgebraicGeometry.Scheme.QCoh.pushforward
          (CategoryTheory.Limits.pullback.snd f g)).obj
        ((AlgebraicGeometry.Scheme.QCoh.tensorRight K).obj
          ((AlgebraicGeometry.Scheme.QCoh.pullback
              (CategoryTheory.Limits.pullback.fst f g)).obj F)))

#check (AlgebraicGeometry.Scheme.QCoh.fourierMukaiFunctor :
  ∀ {R : Type u} [CommRing R] {X Y : AlgebraicGeometry.Scheme.{u}},
    (x : X ⟶ Spec (CommRingCat.of R)) →
    (y : Y ⟶ Spec (CommRingCat.of R)) →
    [CompactSpace X] → [QuasiSeparatedSpace X] →
    AlgebraicGeometry.Scheme.QCoh (CategoryTheory.Limits.pullback x y) →
      (AlgebraicGeometry.Scheme.QCoh X ⥤ AlgebraicGeometry.Scheme.QCoh Y))

#check (AlgebraicGeometry.Scheme.QCoh.fourierMukaiFunctor_obj :
  ∀ {R : Type u} [CommRing R] {X Y : AlgebraicGeometry.Scheme.{u}},
    (x : X ⟶ Spec (CommRingCat.of R)) →
    (y : Y ⟶ Spec (CommRingCat.of R)) →
    [CompactSpace X] → [QuasiSeparatedSpace X] →
    (K : AlgebraicGeometry.Scheme.QCoh (CategoryTheory.Limits.pullback x y)) →
    (F : AlgebraicGeometry.Scheme.QCoh X) →
    (AlgebraicGeometry.Scheme.QCoh.fourierMukaiFunctor x y K).obj F =
      (AlgebraicGeometry.Scheme.QCoh.pushforward
          (CategoryTheory.Limits.pullback.snd x y)).obj
        ((AlgebraicGeometry.Scheme.QCoh.tensorRight K).obj
          ((AlgebraicGeometry.Scheme.QCoh.pullback
              (CategoryTheory.Limits.pullback.fst x y)).obj F)))
