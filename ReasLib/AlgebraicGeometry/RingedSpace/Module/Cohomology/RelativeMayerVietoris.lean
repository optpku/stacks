/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Pushforward.Comparison
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relative Mayer--Vietoris cohomology

This leaf owns the initial relative Mayer--Vietoris window for a morphism of ringed spaces.  The
underived row is canonical; the connecting morphism into the first higher direct image is kept as
an explicit source-level datum because the statement is genuinely existential.  The two exactness
claims are separated so downstream arguments can use the underived short complex without choosing a
boundary map.
-/

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Cohomology.RelativeMayerVietoris

variable {X Y : RingedSpace.{u}}

/-- The first two arrows in the relative Mayer--Vietoris row compose to zero. -/
@[stacks 01EC "relative Mayer--Vietoris composition is zero"]
theorem comp_zero (f : X ⟶ Y) (U V : Opens X.carrier) (F : X.Modules) :
    ((biprod.lift
        (OpenSubspace.Pushforward.alongUnit f U)
        (OpenSubspace.Pushforward.alongUnit f V)).app F) ≫
      ((biprod.desc
          (OpenSubspace.Pushforward.alongRestriction f
            (inf_le_left : U ⊓ V ≤ U))
          (-(OpenSubspace.Pushforward.alongRestriction f
            (inf_le_right : U ⊓ V ≤ V)))).app F) = 0 := sorry

/-- The canonical underived relative Mayer--Vietoris short complex on `Y`. -/
@[stacks 01EC "underived relative Mayer--Vietoris short complex"]
abbrev shortComplex (f : X ⟶ Y) (U V : Opens X.carrier) (F : X.Modules) :
    ShortComplex Y.Modules :=
  ShortComplex.mk
    ((biprod.lift
        (OpenSubspace.Pushforward.alongUnit f U)
        (OpenSubspace.Pushforward.alongUnit f V)).app F)
    ((biprod.desc
        (OpenSubspace.Pushforward.alongRestriction f
          (inf_le_left : U ⊓ V ≤ U))
        (-(OpenSubspace.Pushforward.alongRestriction f
          (inf_le_right : U ⊓ V ≤ V)))).app F)
    (comp_zero f U V F)

/-- The first map of the underived relative Mayer--Vietoris row is monic over a two-open cover. -/
@[stacks 01EC "relative Mayer--Vietoris left monomorphism"]
theorem leftMono (f : X ⟶ Y) (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (F : X.Modules) : Mono (shortComplex f U V F).f := sorry

/-- Exactness at the middle term of the underived relative Mayer--Vietoris row. -/
@[stacks 01EC "relative Mayer--Vietoris middle exactness"]
theorem middleExact (f : X ⟶ Y) (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (F : X.Modules) : (shortComplex f U V F).Exact := sorry

/-- The relative Mayer--Vietoris four-term segment determined by a boundary morphism `δ`. -/
@[stacks 01EC "relative Mayer--Vietoris four-term sequence"]
abbrev sequence (f : X ⟶ Y) (U V : Opens X.carrier) (F : X.Modules)
    (δ : (OpenSubspace.Pushforward.along f (U ⊓ V)).obj F ⟶ higherDirectImageModule f F 1) :
    ComposableArrows Y.Modules 3 :=
  ComposableArrows.mk₃
    ((biprod.lift
        (OpenSubspace.Pushforward.alongUnit f U)
        (OpenSubspace.Pushforward.alongUnit f V)).app F)
    ((biprod.desc
        (OpenSubspace.Pushforward.alongRestriction f
          (inf_le_left : U ⊓ V ≤ U))
        (-(OpenSubspace.Pushforward.alongRestriction f
          (inf_le_right : U ⊓ V ≤ V)))).app F)
    δ

/-- Existence of a boundary morphism making the relative Mayer--Vietoris four-term segment exact. -/
@[stacks 01EC "relative Mayer--Vietoris exact segment"]
theorem existsExact (f : X ⟶ Y) (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (F : X.Modules) :
    ∃ δ : (OpenSubspace.Pushforward.along f (U ⊓ V)).obj F ⟶ higherDirectImageModule f F 1,
      (sequence f U V F δ).Exact := sorry

/-- Existence of a boundary morphism for the initial relative Mayer--Vietoris segment beginning at
`0`; the first map is recorded together with the exact four-term window. -/
@[stacks 01EC "initial relative Mayer--Vietoris exact segment"]
theorem existsInitial (f : X ⟶ Y) (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (F : X.Modules) :
    ∃ δ : (OpenSubspace.Pushforward.along f (U ⊓ V)).obj F ⟶ higherDirectImageModule f F 1,
      Mono (shortComplex f U V F).f ∧ (sequence f U V F δ).Exact := sorry

end AlgebraicGeometry.RingedSpace.Module.Cohomology.RelativeMayerVietoris
