/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.BaseChange.RightAdjoint.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange

universe u

/- Lemma 86.5.1 (1): in cartesian Tor-independent diagram 86.4.0.1 of algebraic
spaces over S, with g a morphism of affine schemes and f proper, flat, and of
finite presentation, the 86.4.1.1 mate L(g')^* a(K) ⟶ a'(Lg^* K) is an
isomorphism for all K : DerivedQCoh Y. -/
@[stacks 0E5I] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange.twistedMap_app_isIso_of_flat :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsAffine Y] [IsAffine Y'] [Proper f] [Flat f] [FinitePresentation f]
    [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (K : DerivedQCoh Y),
    IsIso ((twistedMap g' f' f g sq a a' fAdj f'Adj hTor).app K))

/- Lemma 86.5.1 (2): in cartesian Tor-independent diagram 86.4.0.1 of algebraic
spaces over S, with g a morphism of affine schemes, f proper and perfect, and Y
Noetherian, the 86.4.1.1 mate L(g')^* a(K) ⟶ a'(Lg^* K) is an isomorphism for
all K : DerivedQCoh Y. -/
@[stacks 0E5I] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange.twistedMap_app_isIso_of_perfect :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsAffine Y] [IsAffine Y'] [Proper f] [Perfect f] [IsNoetherian Y]
    [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (K : DerivedQCoh Y),
    IsIso ((twistedMap g' f' f g sq a a' fAdj f'Adj hTor).app K))

/- Lemma 86.5.1 (3): in cartesian Tor-independent diagram 86.4.0.1 of algebraic
spaces over S, with g a morphism of affine schemes of finite Tor dimension, f
proper, and Y Noetherian, the 86.4.1.1 mate L(g')^* a(K) ⟶ a'(Lg^* K) is an
isomorphism for all K : DerivedQCoh Y with K.obj.IsBoundedBelow. -/
@[stacks 0E5I] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange.twistedMap_app_isIso_of_finiteTorDimension :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsAffine Y] [IsAffine Y'] [Proper f] [IsNoetherian Y]
    [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (K : DerivedQCoh Y) (hK : K.obj.IsBoundedBelow)
    (h_finiteTor : ModuleDerived.HasFiniteTorDimensionOver g (DerivedQCoh.structureSheaf Y').obj),
    IsIso ((twistedMap g' f' f g sq a a' fAdj f'Adj hTor).app K))
