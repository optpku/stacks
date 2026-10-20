/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Covering
public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardEtale
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Zariski
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-!
# Étale sites in chosen big-site presentations

This module defines the big slice and small étale site of a chosen presentation.
It also shows that standard étale and Zariski covering families can be represented
by covering families in the chosen big étale site.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty

universe u v

namespace AlgebraicGeometry

/-- An explicit small presentation of a big étale site. -/
abbrev ChosenBigEtaleSite : Type (max (u + 1) (v + 1)) :=
  ChosenBigSite.{u, v} Scheme.etalePrecoverage

end AlgebraicGeometry

namespace AlgebraicGeometry.ChosenBigSite

variable (X : ChosenBigSite.{u, v} Scheme.etalePrecoverage) (T : X.carrier)

/-- Every standard étale cover of the underlying affine scheme of a chosen-site
object is tautologically equivalent to the image of a covering family in the
chosen carrier. -/
theorem exists_coveringFamily_tautologicallyEquivalent_standardEtaleCover
    [IsAffine (X.toScheme.obj T)]
    (𝒰 : StandardEtaleCover (X.toScheme.obj T)) :
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
      Limits.FormalCoproduct.IsCovering
          (@Pretopology.toPrecoverage X.carrier (Cat.str X.carrier)
            X.hasPullbacks X.pretopology) 𝒱 ∧
        Limits.FormalCoproduct.TautologicallyEquivalent
          (Limits.FormalCoproduct.ofArrows
            (fun j : ULift.{u} (Fin 𝒰.n) ↦ 𝒰.U j.down)
            (fun j : ULift.{u} (Fin 𝒰.n) ↦ 𝒰.map j.down))
          ((Limits.FormalCoproduct.map (Over.post (X := T) X.toScheme)).obj 𝒱) := sorry

namespace Etale

/-- Every Zariski open cover of the underlying scheme of a chosen-site object is
tautologically equivalent to the image of a covering family in the chosen
étale carrier. -/
theorem exists_coveringFamily_tautologicallyEquivalent_zariskiCover
    (𝒰 : (X.toScheme.obj T).OpenCover.{u}) :
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
      Limits.FormalCoproduct.IsCovering
          (@Pretopology.toPrecoverage X.carrier (Cat.str X.carrier)
            X.hasPullbacks X.pretopology) 𝒱 ∧
        Limits.FormalCoproduct.TautologicallyEquivalent
          (Limits.FormalCoproduct.ofArrows 𝒰.X 𝒰.f)
          ((Limits.FormalCoproduct.map (Over.post (X := T) X.toScheme)).obj 𝒱) := sorry

end Etale

end AlgebraicGeometry.ChosenBigSite

namespace AlgebraicGeometry.ChosenBigEtaleSite

/-- The carrier of the big étale site over an object in a chosen presentation
is its slice category. -/
abbrev bigSite (X : ChosenBigEtaleSite.{u, v}) (S : X.carrier) :=
  Over S

/-- The big étale topology over an object in a chosen presentation is the
slice topology induced by the chosen big-site topology. -/
def bigTopology (X : ChosenBigEtaleSite.{u, v}) (S : X.carrier) :
    GrothendieckTopology (bigSite X S) :=
  (X.toGrothendieck).over S

/-- The source-scheme functor from a chosen big étale slice. -/
def bigToScheme (X : ChosenBigEtaleSite.{u, v}) (S : X.carrier) :
    bigSite X S ⥤ Scheme.{u} :=
  Over.forget S ⋙ X.toScheme

/-- The object property selecting represented étale structural morphisms in a
chosen big étale slice. -/
def smallObjects (X : ChosenBigEtaleSite.{u, v}) (S : X.carrier) :
    ObjectProperty (bigSite X S) :=
  fun U ↦ Etale (X.toScheme.map U.hom)

/-- The carrier of the small étale site is the full subcategory of a chosen
big slice on represented étale structural morphisms. -/
abbrev smallSite (X : ChosenBigEtaleSite.{u, v}) (S : X.carrier) :=
  ObjectProperty.FullSubcategory (smallObjects X S)

/-- The inclusion of the chosen small étale site into its big slice. -/
def smallInclusion (X : ChosenBigEtaleSite.{u, v}) (S : X.carrier) :
    smallSite X S ⥤ bigSite X S :=
  ObjectProperty.ι (smallObjects X S)

/-- The source-scheme functor from the chosen small étale site. -/
def smallToScheme (X : ChosenBigEtaleSite.{u, v}) (S : X.carrier) :
    smallSite X S ⥤ Scheme.{u} :=
  smallInclusion X S ⋙ bigToScheme X S

/-- The represented structural morphism of every object of the chosen small
étale site is étale. -/
theorem smallSite_obj_isEtale (X : ChosenBigEtaleSite.{u, v})
    (S : X.carrier) (U : smallSite X S) :
    Etale (X.toScheme.map U.obj.hom) := sorry

/-- The precoverage on the chosen small étale site obtained by restricting
covering families from the chosen big slice. -/
def smallPrecoverage (X : ChosenBigEtaleSite.{u, v}) (S : X.carrier) :
    Precoverage (smallSite X S) :=
  (bigTopology X S).toPrecoverage.comap (smallInclusion X S)

/-- A family covers in the chosen small-site precoverage exactly when its
image covers in the chosen big slice. -/
theorem mem_smallPrecoverage_iff (X : ChosenBigEtaleSite.{u, v})
    (S : X.carrier) {U : smallSite X S} {R : Presieve U} :
    R ∈ smallPrecoverage X S U ↔
      R.map (smallInclusion X S) ∈ (bigTopology X S).toPrecoverage U.obj := sorry

/-- The Grothendieck topology on the chosen small étale carrier generated by
its inherited precoverage. -/
def smallTopology (X : ChosenBigEtaleSite.{u, v}) (S : X.carrier) :
    GrothendieckTopology (smallSite X S) :=
  (smallPrecoverage X S).toGrothendieck

end AlgebraicGeometry.ChosenBigEtaleSite
