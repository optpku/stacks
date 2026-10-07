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
derived-pushforward composition isomorphism. -/
@[stacks 0D5T]
#check (iso f g h_pullback : R(f)_* ⋙ R(g)_* ≅ R((f ≫ g))_*)

@[stacks 0D5T]
#check (comparison f g h_pullback : R((f ≫ g))_* ⟶ R(f)_* ⋙ R(g)_*)

@[stacks 0D5T]
#check (comparison_isIso f g h_pullback : IsIso (comparison f g h_pullback))

end AlgebraicGeometry.RingedSpace
