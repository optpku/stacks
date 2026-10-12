/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation

/-!
# Zariski sites in a chosen big-site presentation

This module defines the slice Zariski site represented by a chosen small
presentation and its full subsite of represented open immersions.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty

universe u v

namespace AlgebraicGeometry.ChosenBigZariskiSite

/-- The carrier of the big Zariski site over an object in a chosen
presentation is its slice category. -/
abbrev bigSite (X : ChosenBigZariskiSite.{u, v}) (S : X.carrier) :=
  Over S

/-- The big Zariski topology over an object in a chosen presentation is the
slice topology induced by the chosen big-site topology. -/
def bigTopology (X : ChosenBigZariskiSite.{u, v}) (S : X.carrier) :
    GrothendieckTopology (bigSite X S) :=
  (X.toGrothendieck).over S

/-- The source-scheme functor from a chosen big Zariski slice. -/
def bigToScheme (X : ChosenBigZariskiSite.{u, v}) (S : X.carrier) :
    bigSite X S ⥤ Scheme.{u} :=
  Over.forget S ⋙ X.toScheme

/-- The object property selecting represented open immersions in a chosen
big Zariski slice. -/
def smallObjects (X : ChosenBigZariskiSite.{u, v}) (S : X.carrier) :
    ObjectProperty (bigSite X S) :=
  fun U ↦ IsOpenImmersion (X.toScheme.map U.hom)

/-- The carrier of the small Zariski site is the full subcategory of a chosen
big slice on represented open immersions. -/
abbrev smallSite (X : ChosenBigZariskiSite.{u, v}) (S : X.carrier) :=
  ObjectProperty.FullSubcategory (smallObjects X S)

/-- The inclusion of the chosen small Zariski site into its big slice. -/
def smallInclusion (X : ChosenBigZariskiSite.{u, v}) (S : X.carrier) :
    smallSite X S ⥤ bigSite X S :=
  ObjectProperty.ι (smallObjects X S)

/-- The source-scheme functor from the chosen small Zariski site. -/
def smallToScheme (X : ChosenBigZariskiSite.{u, v}) (S : X.carrier) :
    smallSite X S ⥤ Scheme.{u} :=
  smallInclusion X S ⋙ bigToScheme X S

/-- The represented structural morphism of every object of the chosen small
Zariski site is an open immersion. -/
theorem smallSite_obj_isOpenImmersion (X : ChosenBigZariskiSite.{u, v})
    (S : X.carrier) (U : smallSite X S) :
    IsOpenImmersion (X.toScheme.map U.obj.hom) := sorry

/-- The precoverage on the chosen small Zariski site obtained by restricting
covering families from the chosen big slice. -/
def smallPrecoverage (X : ChosenBigZariskiSite.{u, v}) (S : X.carrier) :
    Precoverage (smallSite X S) :=
  (bigTopology X S).toPrecoverage.comap (smallInclusion X S)

/-- A family covers in the chosen small-site precoverage exactly when its
image covers in the chosen big slice. -/
theorem mem_smallPrecoverage_iff (X : ChosenBigZariskiSite.{u, v})
    (S : X.carrier) {U : smallSite X S} {R : Presieve U} :
    R ∈ smallPrecoverage X S U ↔
      R.map (smallInclusion X S) ∈ (bigTopology X S).toPrecoverage U.obj := sorry

/-- The Grothendieck topology on the chosen small Zariski carrier generated
by its inherited precoverage. -/
def smallTopology (X : ChosenBigZariskiSite.{u, v}) (S : X.carrier) :
    GrothendieckTopology (smallSite X S) :=
  (smallPrecoverage X S).toGrothendieck

end AlgebraicGeometry.ChosenBigZariskiSite
