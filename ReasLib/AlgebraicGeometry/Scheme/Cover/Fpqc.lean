/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import ReasLib.CategoryTheory.Sites.Family.Covering

/-!
# Fpqc covering families of schemes

This module relates indexed families in a slice category and fixed-target
scheme covers to the canonical fpqc precoverage. It also gives the finite
affine-refinement characterization of fpqc covering families.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u v

namespace AlgebraicGeometry.Scheme

variable {T : Scheme.{u}} {ι : Type v}

/-- An indexed family over `T` is fpqc-covering when its arrows form a cover
for the canonical fpqc precoverage. -/
@[stacks 022B]
abbrev FpqcCovering (family : ι → Over T) : Prop :=
  IsCovering Scheme.fpqcPrecoverage
    (ofArrows (fun i ↦ (family i).left) fun i ↦ (family i).hom)

/-- An indexed family is fpqc-covering exactly when its arrows generate a
covering presieve for the canonical fpqc precoverage. -/
theorem fpqcCovering_iff_mem_precoverage (family : ι → Over T) :
    FpqcCovering family ↔
      Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
        Scheme.fpqcPrecoverage.coverings T := sorry

/-- The indexed-family formulation agrees with the fixed-target family
covering predicate. -/
theorem fpqcCovering_obj_iff_isCovering
    (𝒰 : CategoryTheory.SemiRepresentableFamily.Over T) :
    FpqcCovering 𝒰.obj ↔
      CategoryTheory.SemiRepresentableFamily.Over.IsCovering Scheme.fpqcPrecoverage 𝒰 := sorry

/-- The arrows of an fpqc-covering indexed family generate an fpqc covering
presieve. -/
theorem FpqcCovering.mem_fpqc_precoverage
    {family : ι → Over T} (h : FpqcCovering family) :
    Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
      Scheme.fpqcPrecoverage.coverings T := sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

variable {T : Scheme.{u}} {ι : Type v}

/-- The finite affine-refinement condition for an indexed family of morphisms
to `T`: every affine open of `T` is the union of images of finitely many
affine opens drawn from the family. -/
def HasAffineRefinement (family : ι → Over T) : Prop :=
  ∀ U : T.Opens, IsAffineOpen U →
    ∃ n : ℕ,
      ∃ a : Fin n → ι,
        ∃ V : (j : Fin n) → ((family (a j)).left).Opens,
          (∀ j : Fin n, IsAffineOpen (V j)) ∧
            (⋃ j : Fin n, (family (a j)).hom.base '' (V j : Set (family (a j)).left.carrier)) =
              (U : Set T.carrier)

/-- An indexed family over `T` is an fpqc covering when its members are flat
and it admits a finite affine refinement over every affine open of `T`. -/
def IsFpqcCovering (family : ι → Over T) : Prop :=
  (∀ i : ι, Flat (family i).hom) ∧ HasAffineRefinement family

/-- The finite affine-refinement characterization of the canonical fpqc
covering predicate. -/
theorem fpqcCovering_iff_flat_and_hasAffineRefinement (family : ι → Over T) :
    Scheme.FpqcCovering family ↔
      (∀ i : ι, Flat (family i).hom) ∧ HasAffineRefinement family := sorry

/-- An `IsFpqcCovering` witness gives the canonical indexed fpqc-covering
predicate. -/
theorem IsFpqcCovering.fpqcCovering
    {family : ι → Over T} (h : IsFpqcCovering family) :
    Scheme.FpqcCovering family := sorry

/-- An fpqc covering family consists exactly of flat morphisms and finite
affine refinements over every affine open of the target. -/
theorem IsFpqcCovering.source_spec
    {family : ι → Over T} (h : IsFpqcCovering family) :
    (∀ i : ι, Flat (family i).hom) ∧ HasAffineRefinement family := sorry

/-- Every member of an fpqc covering family is flat. -/
theorem IsFpqcCovering.flat
    {family : ι → Over T} (h : IsFpqcCovering family) (i : ι) :
    Flat (family i).hom := sorry

/-- The finite affine-refinement projection of an fpqc-covering family. -/
theorem IsFpqcCovering.affine_refinement
    {family : ι → Over T} (h : IsFpqcCovering family) :
    HasAffineRefinement family := sorry

/-- An fpqc covering admits its defining finite affine refinement over every
affine open of the target. -/
theorem IsFpqcCovering.exists_affine_refinement
    {family : ι → Over T} (h : IsFpqcCovering family)
    (U : T.Opens) (hU : IsAffineOpen U) :
    ∃ n : ℕ,
      ∃ a : Fin n → ι,
        ∃ V : (j : Fin n) → ((family (a j)).left).Opens,
          (∀ j : Fin n, IsAffineOpen (V j)) ∧
            (⋃ j : Fin n, (family (a j)).hom.base '' (V j : Set (family (a j)).left.carrier)) =
              (U : Set T.carrier) := sorry

/-- A fixed-target fpqc cover in the canonical fpqc precoverage. -/
abbrev FpqcCover (T : Scheme.{u}) :=
  T.Cover Scheme.fpqcPrecoverage

namespace FpqcCover

/-- The arrows of an fpqc cover generate a covering presieve for the
canonical fpqc precoverage. -/
theorem mem_fpqc_precoverage (𝒰 : FpqcCover T) :
    Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage.coverings T := sorry

/-- The indexed `Over T` family underlying a fixed-target fpqc cover is an
fpqc-covering family. -/
theorem fpqcCovering (𝒰 : FpqcCover T) :
    Scheme.FpqcCovering (fun i : 𝒰.I₀ ↦ Over.mk (𝒰.f i)) := sorry

/-- Each member of a fixed-target fpqc cover is flat. -/
theorem flat (𝒰 : FpqcCover T) (i : 𝒰.I₀) :
    Flat (𝒰.f i) := sorry

end FpqcCover

end AlgebraicGeometry
