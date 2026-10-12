/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Limits

/-!
# Affine objects in chosen big-site slices

This module defines the full subcategory of a chosen big-site slice whose
represented source schemes are affine, together with its canonical functors
and pullback properties.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigSite

variable {P : Precoverage Scheme.{u}} (X : ChosenBigSite.{u, v} P)
  (S : X.carrier)

/-- The object property on a chosen big-site slice selecting objects whose
represented source schemes are affine. -/
def affineObjects : ObjectProperty (Over S) :=
  fun U ↦ IsAffine (X.toScheme.obj U.left)

/-- An object belongs to `affineObjects X S` exactly when its represented
source scheme is affine. -/
theorem mem_affineObjects (U : Over S) :
    affineObjects X S U ↔ IsAffine (X.toScheme.obj U.left) := sorry

/-- The affine-source carrier over `S` is the full subcategory of the chosen
big-site slice on affine represented sources. -/
abbrev affineSite := ObjectProperty.FullSubcategory (affineObjects X S)

/-- The inclusion of the affine-source carrier into the chosen big-site slice. -/
def affineInclusion : affineSite X S ⥤ Over S :=
  ObjectProperty.ι (affineObjects X S)

/-- The functor from the affine-source carrier to schemes sends an object to
its represented source scheme. -/
def affineToScheme : affineSite X S ⥤ Scheme.{u} :=
  affineInclusion X S ⋙ sliceToScheme X S

/-- The affine-source functor evaluates to the represented source scheme. -/
theorem affineToScheme_obj (U : affineSite X S) :
    (affineToScheme X S).obj U = X.toScheme.obj U.obj.left := sorry

/-- Affine-source objects of a chosen big-site slice are closed under pullbacks. -/
theorem affineObjectsIsClosedUnderPullbacks :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (affineObjects X S) Limits.WalkingCospan := sorry

/-- The affine-source carrier of a chosen big-site slice has pullbacks. -/
theorem affineSiteHasPullbacks : Limits.HasPullbacks (affineSite X S) := sorry

/-- The source-scheme functor from an affine-source carrier preserves pullbacks. -/
theorem affineToSchemePreservesPullbacks :
    Limits.PreservesLimitsOfShape Limits.WalkingCospan
      (affineToScheme X S) := sorry

end AlgebraicGeometry.ChosenBigSite
