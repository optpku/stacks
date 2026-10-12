/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Linearity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.QCoh

/-- The ambient tensor product preserves quasicoherence, so it can be restricted
to the full subcategory `Scheme.QCoh`. -/
theorem tensorRightPreservesQuasiCoherent {P : Scheme.{u}} (K : Scheme.QCoh P) :
    Scheme.quasiCoherentModuleProperty P ≤
      (Scheme.quasiCoherentModuleProperty P).inverseImage
        (CategoryTheory.MonoidalCategory.tensorRight K.obj) := sorry

/-- The tensor-by-kernel functor on quasicoherent modules. -/
noncomputable def tensorRight {P : Scheme.{u}} (K : Scheme.QCoh P) :
    Scheme.QCoh P ⥤ Scheme.QCoh P :=
  ObjectProperty.FullSubcategory.restrict
    (CategoryTheory.MonoidalCategory.tensorRight K.obj)
    (tensorRightPreservesQuasiCoherent K)

/-- The underlying module of `tensorRight K` is the ambient tensor product. -/
theorem tensorRight_obj {P : Scheme.{u}} (K : Scheme.QCoh P) (F : Scheme.QCoh P) :
    ((tensorRight K).obj F).obj =
      (CategoryTheory.MonoidalCategory.tensorRight K.obj).obj F.obj := sorry

/-- The underived Fourier--Mukai transform over an arbitrary scheme base. -/
noncomputable def fourierMukai
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact (Limits.pullback.snd f g)]
    [QuasiSeparated (Limits.pullback.snd f g)]
    (K : Scheme.QCoh (Limits.pullback f g)) :
    Scheme.QCoh X ⥤ Scheme.QCoh Y :=
  Scheme.QCoh.pullback (Limits.pullback.fst f g) ⋙
    tensorRight K ⋙
      Scheme.QCoh.pushforward (Limits.pullback.snd f g)

/-- The object map of the underived Fourier--Mukai transform is pullback,
tensoring by the kernel, followed by pushforward. -/
theorem fourierMukai_obj
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact (Limits.pullback.snd f g)]
    [QuasiSeparated (Limits.pullback.snd f g)]
    (K : Scheme.QCoh (Limits.pullback f g)) (F : Scheme.QCoh X) :
    (fourierMukai f g K).obj F =
      (Scheme.QCoh.pushforward (Limits.pullback.snd f g)).obj
        ((tensorRight K).obj
          ((Scheme.QCoh.pullback (Limits.pullback.fst f g)).obj F)) := sorry

/-- The affine-base Fourier--Mukai functor is the pullback--tensor--pushforward
composition associated to two scheme morphisms over an affine scheme. -/
noncomputable def fourierMukaiFunctor
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R))
    [CompactSpace X] [QuasiSeparatedSpace X]
    (K : Scheme.QCoh (Limits.pullback x y)) :
    Scheme.QCoh X ⥤ Scheme.QCoh Y :=
  fourierMukai x y K

/-- The object map of the affine-base Fourier--Mukai functor is pullback,
tensoring by the kernel, followed by pushforward. -/
theorem fourierMukaiFunctor_obj
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R))
    [CompactSpace X] [QuasiSeparatedSpace X]
    (K : Scheme.QCoh (Limits.pullback x y)) (F : Scheme.QCoh X) :
    (fourierMukaiFunctor x y K).obj F =
      (Scheme.QCoh.pushforward (Limits.pullback.snd x y)).obj
        ((tensorRight K).obj
          ((Scheme.QCoh.pullback (Limits.pullback.fst x y)).obj F)) := sorry

namespace fourierMukaiFunctor

/-- The affine-base Fourier–Mukai functor is relatively linear for the scalar
structures induced by the two structure morphisms. -/
instance linear
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))
    [CompactSpace X] [QuasiSeparatedSpace X]
    (K : Scheme.QCoh (Limits.pullback x y)) :
    Scheme.QCoh.LinearOver x y (fourierMukaiFunctor x y K) := sorry

/-- The affine-base Fourier–Mukai functor preserves arbitrary coproducts. -/
instance preservesCoproducts
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))
    [CompactSpace X] [QuasiSeparatedSpace X]
    (K : Scheme.QCoh (Limits.pullback x y)) (J : Type w) :
    PreservesColimitsOfShape (Discrete J) (fourierMukaiFunctor x y K) := sorry

end fourierMukaiFunctor

end AlgebraicGeometry.Scheme.QCoh
