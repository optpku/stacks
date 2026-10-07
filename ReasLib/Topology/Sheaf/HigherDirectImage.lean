module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.Topology.Sheaf.Pushforward
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Higher Direct Images on Topological Spaces

This file owns the classical higher direct images of sheaves of abelian groups along continuous
maps. The functor, its values and maps, and the injective-resolution computation are available
without importing a textbook chapter.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

/-- The degree-`i` higher direct image functor on sheaves of abelian groups along a continuous
map. -/
abbrev higherDirectImageFunctor
    {X Y : TopCat.{u}}
    (f : X ⟶ Y) (i : ℕ) :
    X.Sheaf AddCommGrpCat.{u} ⥤ Y.Sheaf AddCommGrpCat.{u} :=
  (pushforward AddCommGrpCat.{u} f).rightDerived i

/-- The degree-`i` higher direct image of a sheaf of abelian groups along a continuous map. -/
@[stacks 0713 "topological higher direct image"]
abbrev higherDirectImage
    {X Y : TopCat.{u}}
    (f : X ⟶ Y) (F : X.Sheaf AddCommGrpCat.{u}) (i : ℕ) :
    Y.Sheaf AddCommGrpCat.{u} :=
  (higherDirectImageFunctor f i).obj F

/-- The map on higher direct images induced by a morphism of sheaves of abelian groups. -/
abbrev higherDirectImageMap
    {X Y : TopCat.{u}}
    (f : X ⟶ Y) {F G : X.Sheaf AddCommGrpCat.{u}} (a : F ⟶ G) (i : ℕ) :
    higherDirectImage f F i ⟶ higherDirectImage f G i :=
  (higherDirectImageFunctor f i).map a

namespace HigherDirectImage

/-- A chosen injective resolution computes the higher direct image through the homology of its
pushforward. -/
@[stacks 0713 "injective-resolution computation"]
noncomputable abbrev isoHomologyPushforward
    {X Y : TopCat.{u}}
    (f : X ⟶ Y) (F : X.Sheaf AddCommGrpCat.{u}) (I : InjectiveResolution F) (i : ℕ) :
    higherDirectImage f F i ≅
      (HomologicalComplex.homologyFunctor
        (Y.Sheaf AddCommGrpCat.{u}) (ComplexShape.up ℕ) i).obj
        (((pushforward AddCommGrpCat.{u} f).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) :=
  I.isoRightDerivedObj (pushforward AddCommGrpCat.{u} f) i

end HigherDirectImage

end TopCat.Sheaf
