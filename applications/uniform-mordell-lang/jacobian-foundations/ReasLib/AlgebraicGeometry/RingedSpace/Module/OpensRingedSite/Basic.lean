module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.AlgebraicGeometry.RingedSite.Localization
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.Topology.Sheaves.Abelian.Over
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The opens ringed site of a ringed space

This file owns the canonical ringed site of open subsets and the sheafification instances on its
localizations.  It deliberately stays below both complex and derived module infrastructure.
-/

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The commutative ringed site of opens of a ringed space, equipped with its structure sheaf. -/
@[stacks 03DF "opens ringed site"]
abbrev opensRingedSite (X : RingedSpace.{u}) :=
  RingedSite.ofCommRingSheaf (Opens.grothendieckTopology X) X.sheaf

namespace OpensRingedSite

/-- Abelian-group-valued weak sheafification is available uniformly on localizations of the
opens ringed site of a ringed space. -/
@[stacks 03DF "abelian sheafification on localized opens sites"]
instance localizationHasWeakSheafify (X : RingedSpace.{u}) :
    ∀ U : (opensRingedSite X).carrier,
      HasWeakSheafify ((opensRingedSite X).localization U).siteTopology
        AddCommGrpCat.{u} := sorry

/-- Local bijectivity on every localization of an opens ringed site agrees with the weak
equivalences used by sheafification. -/
@[stacks 03DF "local bijectivity on localized opens sites"]
instance localizationWEqualsLocallyBijective (X : RingedSpace.{u}) :
    ∀ U : (opensRingedSite X).carrier,
      ((opensRingedSite X).localization U).siteTopology.WEqualsLocallyBijective
        AddCommGrpCat.{u} := sorry

/-- Abelian-group-valued weak sheafification is available uniformly after two successive
localizations of an opens ringed site. -/
@[stacks 03DF "abelian sheafification on iterated localized opens sites"]
instance iteratedLocalizationHasWeakSheafify (X : RingedSpace.{u}) :
    ∀ (U : (opensRingedSite X).carrier)
      (V : ((opensRingedSite X).localization U).carrier),
      HasWeakSheafify
        (((opensRingedSite X).localization U).localization V).siteTopology
        AddCommGrpCat.{u} := sorry

/-- Local bijectivity after two successive localizations of an opens ringed site agrees with
the weak equivalences used by sheafification. -/
@[stacks 03DF "local bijectivity on iterated localized opens sites"]
instance iteratedLocalizationWEqualsLocallyBijective (X : RingedSpace.{u}) :
    ∀ (U : (opensRingedSite X).carrier)
      (V : ((opensRingedSite X).localization U).carrier),
      (((opensRingedSite X).localization U).localization V).siteTopology.WEqualsLocallyBijective
        AddCommGrpCat.{u} := sorry

end OpensRingedSite

end AlgebraicGeometry.RingedSpace

