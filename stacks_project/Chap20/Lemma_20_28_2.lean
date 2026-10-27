/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Composition
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

universe u

namespace AlgebraicGeometry.RingedSpace

open Hom
open moduleDerivedPushforward.Composition

variable {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable (h_pullback : IsIso (modulePullbackDerived.compComparison f g))
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules Y)]
variable [CategoryWithHomology (RingedSpace.Modules Z)]
variable [(pushforward f).Additive] [(pushforward g).Additive]
variable [(pullback f).Additive] [(pullback g).Additive]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [RingedSite.Hom.DerivedAdjunction.HasPair (opensRingedSiteHom f)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair (opensRingedSiteHom g)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair (opensRingedSiteHom (f ≫ g))]

/- Lemma 20.28.2: morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z` satisfy
`R(f)_* ⋙ R(g)_* = R((f ≫ g))_*` as functors `D(O_X) ⟶ D(O_Z)`, via the specified
derived-pushforward composition isomorphism. Stacks states this unconditionally and uses the
derived-pullback composition isomorphism, which is valid for all morphisms of ringed spaces.
At the current library boundary, `h_pullback` explicitly supplies the invertibility certificate
for the canonical derived-pullback composition comparison. -/
@[stacks 0D5T]
#check (AlgebraicGeometry.RingedSpace.moduleDerivedPushforward.Composition.iso f g h_pullback :
  R(f)_* ⋙ R(g)_* ≅ R((f ≫ g))_*)

@[stacks 0D5T]
#check (AlgebraicGeometry.RingedSpace.moduleDerivedPushforward.Composition.comparison
  f g h_pullback : R((f ≫ g))_* ⟶ R(f)_* ⋙ R(g)_*)

@[stacks 0D5T]
#check (AlgebraicGeometry.RingedSpace.moduleDerivedPushforward.Composition.comparison_isIso
  f g h_pullback :
  IsIso (AlgebraicGeometry.RingedSpace.moduleDerivedPushforward.Composition.comparison
    f g h_pullback))

end AlgebraicGeometry.RingedSpace
