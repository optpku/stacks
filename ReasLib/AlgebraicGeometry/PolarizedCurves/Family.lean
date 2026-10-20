/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.Polarized.ToSpaces
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category

/-!
# Polarized curves

`PolarizedCurves` is the full subcategory of Polarized on families of relative
dimension at most 1. Equivalently, it parametrizes polarized scheme families
`(X ⟶ S, L)` that are proper, flat, finitely presented, of relative dimension
at most 1, with `L` relatively ample.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.PolarizedCurves

/-- The object property of polarized families of relative dimension at most 1. -/
def mem : ObjectProperty Polarized.Obj :=
  fun x ↦ Scheme.Hom.RelativeDimensionLE x.hom 1

/-- Membership in `mem` is the relative-dimension bound on the structure
morphism. -/
theorem mem_iff (x : Polarized.Obj) :
    mem x ↔ Scheme.Hom.RelativeDimensionLE x.hom 1 :=
  sorry

/-- Polarized families of curves: the full subcategory of Polarized on objects
whose structure morphism has relative dimension at most 1. -/
abbrev Obj := mem.FullSubcategory

/-- Package a polarized family of relative dimension at most 1 as an object of
PolarizedCurves. -/
def mk (x : Polarized.Obj) [h : Scheme.Hom.RelativeDimensionLE x.hom 1] : Obj where
  obj := x
  property := h

/-- The underlying polarized object of `mk x` is `x`. -/
theorem mk_obj (x : Polarized.Obj) [Scheme.Hom.RelativeDimensionLE x.hom 1] :
    (mk x).obj = x :=
  sorry

/-- An object of PolarizedCurves is a polarized family of relative dimension at
most 1. -/
theorem spec (P : Obj) :
    Scheme.Hom.RelativeDimensionLE P.obj.hom 1 :=
  sorry

/-- The full-subcategory inclusion PolarizedCurves ⥤ Polarized. -/
abbrev inclusion : Obj ⥤ Polarized.Obj :=
  mem.ι

/-- The inclusion of PolarizedCurves is full. -/
instance instFull_inclusion : inclusion.Full :=
  inferInstance

/-- The inclusion of PolarizedCurves is faithful. -/
instance instFaithful_inclusion : inclusion.Faithful :=
  inferInstance

/-- The inclusion sends `mk x` to `x`. -/
theorem inclusion_obj (x : Polarized.Obj)
    [Scheme.Hom.RelativeDimensionLE x.hom 1] :
    inclusion.obj (mk x) = x :=
  sorry

/-- The forgetful functor sending a polarized curve family to its base scheme. -/
abbrev p : Obj ⥤ Scheme.{u} :=
  inclusion ⋙ Polarized.p

/-- The object part of `p` is the base scheme of the underlying polarized
object. -/
theorem p_obj (P : Obj) : p.obj P = P.obj.S :=
  sorry

/-- Membership in PolarizedCurves is equivalent to the forgotten family lying
in the stack of curves over the terminal scheme. -/
theorem mem_iff_curves (x : Polarized.Obj) :
    mem x ↔
      AlgebraicSpace.Spaces.Curves.relativeDimensionLE (⊤_ Scheme.{u}) 1 (Polarized.toFpFlatProper.obj x) :=
  sorry

end AlgebraicGeometry.PolarizedCurves

namespace AlgebraicGeometry

/-- Polarized families of curves, as the full subcategory of Polarized on
relative dimension at most 1. -/
abbrev PolarizedCurves := PolarizedCurves.Obj

end AlgebraicGeometry
