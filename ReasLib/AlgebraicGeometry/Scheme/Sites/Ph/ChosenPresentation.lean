/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Presentation

/-!
# Ph sites in a chosen big-site presentation

This module defines the slice and affine-source categories represented by an
explicit chosen small `ph` presentation.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty

universe u v

namespace AlgebraicGeometry

namespace ChosenBigPhSite

/-- The carrier of the big ph site over an object in a chosen presentation is
its slice category. -/
abbrev bigSite (X : ChosenBigPhSite.{u, v}) (S : X.carrier) :=
  Over S

/-- The big ph topology over an object in a chosen presentation is the slice
topology induced by the chosen big-site topology. -/
def bigTopology (X : ChosenBigPhSite.{u, v}) (S : X.carrier) :
    GrothendieckTopology (bigSite X S) :=
  (X.toGrothendieck).over S

/-- The source-scheme functor from a chosen big ph slice. -/
def bigToScheme (X : ChosenBigPhSite.{u, v}) (S : X.carrier) :
    bigSite X S ⥤ Scheme.{u} :=
  Over.forget S ⋙ X.toScheme

/-- The object property selecting affine represented source schemes in a
chosen big ph slice. -/
def bigAffineObjects (X : ChosenBigPhSite.{u, v}) (S : X.carrier) :
    ObjectProperty (bigSite X S) :=
  fun U ↦ IsAffine (X.toScheme.obj U.left)

/-- The big affine ph carrier is the full subcategory of the chosen big slice
on objects with affine represented source. -/
abbrev bigAffineSite (X : ChosenBigPhSite.{u, v}) (S : X.carrier) :=
  ObjectProperty.FullSubcategory (bigAffineObjects X S)

/-- The inclusion of the chosen big affine ph carrier into the chosen big
slice. -/
def bigAffineInclusion (X : ChosenBigPhSite.{u, v}) (S : X.carrier) :
    bigAffineSite X S ⥤ bigSite X S :=
  ObjectProperty.ι (bigAffineObjects X S)

/-- The source-scheme functor from the chosen big affine ph carrier. -/
def bigAffineToScheme (X : ChosenBigPhSite.{u, v}) (S : X.carrier) :
    bigAffineSite X S ⥤ Scheme.{u} :=
  bigAffineInclusion X S ⋙ bigToScheme X S

end ChosenBigPhSite

end AlgebraicGeometry
