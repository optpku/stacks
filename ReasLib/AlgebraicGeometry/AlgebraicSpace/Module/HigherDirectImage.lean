/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage

/-!
# Higher direct images of modules on algebraic spaces

The degree-`i` higher direct image of a sheaf of modules along a morphism of algebraic spaces
is the ordinary right derived functor of module pushforward on the small étale ringed sites.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImageFunctor`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Module pushforward along a morphism of algebraic spaces is additive. -/
instance pushforward_additive (f : X ⟶ Y) [Abelian X.Modules] [Abelian Y.Modules] :
    (pushforward f).Additive :=
  sorry

/-- The degree-`i` higher direct image functor of sheaves of modules along a morphism of
algebraic spaces. -/
def higherDirectImageFunctor (f : X ⟶ Y) [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] (i : ℕ) :
    X.Modules ⥤ Y.Modules :=
  (pushforward f).rightDerived i

/-- The degree-`i` higher direct image of a sheaf of modules along a morphism of algebraic
spaces. -/
def higherDirectImage (f : X ⟶ Y) [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) (i : ℕ) : Y.Modules :=
  (higherDirectImageFunctor f i).obj F

/-- The map on higher direct images of modules induced by a morphism of sheaves of modules. -/
def higherDirectImageMap (f : X ⟶ Y) [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] {F G : X.Modules} (φ : F ⟶ G) (i : ℕ) :
    higherDirectImage f F i ⟶ higherDirectImage f G i :=
  (higherDirectImageFunctor f i).map φ

/-- Higher direct image of modules is the object map of `rightDerived` of module pushforward. -/
theorem higherDirectImage_eq (f : X ⟶ Y) [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) (i : ℕ) :
    higherDirectImage f F i = ((pushforward f).rightDerived i).obj F :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
