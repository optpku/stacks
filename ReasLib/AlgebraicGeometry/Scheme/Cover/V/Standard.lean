/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph
public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardFpqc.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Basic

/-!
# Standard-cover bridges for valuative covers

This module relates the standard finite chart presentations already used for
fpqc and proper-surjective covers to the standard valuative-cover predicate.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace StandardFpqcCover

variable {T : Scheme.{u}}

/-- A standard fpqc cover is a standard `V` cover. -/
@[stacks 0ETC]
theorem isStandardVCover (cover : StandardFpqcCover T) :
    AffineFamilyOver.IsStandardVCover (toAffineFamily cover) := sorry

end StandardFpqcCover

namespace StandardPhCovering

variable {T : Scheme.{u}} [IsAffine T]

/-- The finite affine family underlying a standard proper-surjective chart
cover. -/
def toAffineFamily (cover : StandardPhCovering T) : AffineFamilyOver T where
  n := cover.m
  U := cover.obj
  map := cover.map
  isAffine := cover.isAffine_obj

/-- The chart maps of `toAffineFamily` are the original proper-surjective
chart maps. -/
@[simp] theorem toAffineFamily_map (cover : StandardPhCovering T)
    (j : Fin cover.m) :
    (toAffineFamily cover).map j = cover.map j := sorry

/-- A standard proper-surjective chart cover of an affine scheme is a standard
`V` cover. -/
@[stacks 0ETD]
theorem isStandardVCover (cover : StandardPhCovering T) :
    AffineFamilyOver.IsStandardVCover (toAffineFamily cover) := sorry

end StandardPhCovering

end AlgebraicGeometry
