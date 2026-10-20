/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage

/-! # Compatibility checks for higher direct images of modules -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImageFunctor`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

#check (AlgebraicGeometry.AlgebraicSpace.Modules.pushforward_additive :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Abelian X.Modules] [Abelian Y.Modules],
    (pushforward f).Additive)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.higherDirectImageFunctor :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] (i : ℕ),
    X.Modules ⥤ Y.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.higherDirectImage :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) (i : ℕ), Y.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.higherDirectImageMap :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] {F G : X.Modules} (φ : F ⟶ G) (i : ℕ),
    higherDirectImage f F i ⟶ higherDirectImage f G i)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.higherDirectImage_eq :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) (i : ℕ),
    higherDirectImage f F i = ((pushforward f).rightDerived i).obj F)
