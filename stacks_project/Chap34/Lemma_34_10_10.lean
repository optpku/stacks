/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Comparison

@[expose] public section

/-!
# Lemma 34.10.10

This chapter entry is a compatibility facade for comparisons from standard
geometric cover notions to `V` covers.
-/

open CategoryTheory

universe u v

variable {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}

/- Lemma 34.10.10: any fpqc covering is a `V` covering; in particular, this
holds for fppf, syntomic, smooth, étale, and Zariski coverings, and it also
holds for ph coverings. -/
@[stacks 0ETK] #check
  (AlgebraicGeometry.isVCovering_of_fpqcCovering :
    (family : ι → Over T) → AlgebraicGeometry.Scheme.FpqcCovering family →
      AlgebraicGeometry.IsVCovering T (fun i ↦ (family i).left)
        (fun i ↦ (family i).hom))

#check
  (AlgebraicGeometry.isVCovering_of_fppfCover :
    (cover : AlgebraicGeometry.FppfCover T) →
      AlgebraicGeometry.IsVCovering T cover.X cover.f)

#check
  (AlgebraicGeometry.isVCovering_of_syntomicCover :
    (cover : AlgebraicGeometry.SyntomicCover T) →
      AlgebraicGeometry.IsVCovering T cover.X cover.f)

#check
  (AlgebraicGeometry.isVCovering_of_smoothCovering :
    (family : ι → Over T) → AlgebraicGeometry.Scheme.SmoothCovering family →
      AlgebraicGeometry.IsVCovering T (fun i ↦ (family i).left)
        (fun i ↦ (family i).hom))

#check
  (AlgebraicGeometry.isVCovering_of_etaleCovering :
    (cover : AlgebraicGeometry.Scheme.Cover
      AlgebraicGeometry.Scheme.etalePrecoverage T) →
      AlgebraicGeometry.IsVCovering T cover.X cover.f)

#check
  (AlgebraicGeometry.isVCovering_of_zariskiCovering :
    (cover : AlgebraicGeometry.Scheme.OpenCover T) →
      AlgebraicGeometry.IsVCovering T cover.X cover.f)

#check
  (AlgebraicGeometry.isVCovering_of_phCovering :
    {family : ι → AlgebraicGeometry.Scheme.{u}} →
      {map : ∀ i, family i ⟶ T} → AlgebraicGeometry.PhCovering family map →
        AlgebraicGeometry.IsVCovering T family map)
