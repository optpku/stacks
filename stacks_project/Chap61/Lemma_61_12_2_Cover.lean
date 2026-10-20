/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import ReasLib.CategoryTheory.Sites.Family.Covering
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc

/-!
# Pro-étale covering families of schemes

This module relates indexed families in a slice category and fixed-target
scheme covers to the canonical pro-étale precoverage.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u v

namespace AlgebraicGeometry.Scheme

variable {T : Scheme.{u}} {ι : Type v}

/-- An indexed family over `T` is a pro-étale covering when its arrows form a
cover for the canonical pro-étale precoverage. -/
abbrev ProetaleCovering (family : ι → Over T) : Prop :=
  IsCovering Scheme.proetalePrecoverage
    (ofArrows (fun i ↦ (family i).left) fun i ↦ (family i).hom)

/-- An indexed family is a pro-étale covering exactly when its arrows generate
a covering presieve for the canonical pro-étale precoverage. -/
theorem proetaleCovering_iff_mem_precoverage (family : ι → Over T) :
    ProetaleCovering family ↔
      Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
        Scheme.proetalePrecoverage.coverings T := sorry

/-- The arrows of a pro-étale covering indexed family generate a pro-étale
covering presieve. -/
theorem ProetaleCovering.mem_proetale_precoverage
    {family : ι → Over T} (h : ProetaleCovering family) :
    Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
      Scheme.proetalePrecoverage.coverings T := sorry

/-- Every member of a pro-étale covering family is weakly étale. -/
theorem ProetaleCovering.weaklyEtale
    {family : ι → Over T} (h : ProetaleCovering family) :
    ∀ i : ι, WeaklyEtale (family i).hom := sorry

/-- A pro-étale covering family is an fpqc covering family. -/
theorem ProetaleCovering.fpqcCovering
    {family : ι → Over T} (h : ProetaleCovering family) :
    FpqcCovering family := sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

variable {T : Scheme.{u}} {ι : Type v}

/-- The finite affine-refinement characterization of the canonical pro-étale
covering predicate: each member is weakly étale and every affine open of the
target is a finite union of images of affine opens from the family. -/
theorem Scheme.proetaleCovering_iff_hasAffineRefinement (family : ι → Over T) :
    Scheme.ProetaleCovering family ↔
      (∀ i : ι, WeaklyEtale (family i).hom) ∧ HasAffineRefinement family := sorry

/-- A fixed-target pro-étale cover in the canonical pro-étale precoverage. -/
abbrev ProetaleCover (T : Scheme.{u}) :=
  T.Cover Scheme.proetalePrecoverage

namespace ProetaleCover

/-- The arrows of a pro-étale cover generate a covering presieve for the
canonical pro-étale precoverage. -/
theorem mem_proetale_precoverage (𝒰 : ProetaleCover T) :
    Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.proetalePrecoverage.coverings T := sorry

/-- The indexed `Over T` family underlying a fixed-target pro-étale cover is a
pro-étale covering family. -/
theorem proetaleCovering (𝒰 : ProetaleCover T) :
    Scheme.ProetaleCovering (fun i : 𝒰.I₀ ↦ Over.mk (𝒰.f i)) := sorry

end ProetaleCover

end AlgebraicGeometry
