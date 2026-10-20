/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Refinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Stability

/-!
# Comparison maps into valuative covering families

The common geometric cover notions used by the project each induce a `V`
covering family.  Keeping these bridges together lets later site and sheaf
arguments import one neutral comparison leaf.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

variable {T : Scheme.{u}} {ι : Type v}

/-- Every fpqc-covering indexed family is a `V` cover. -/
@[stacks 0ETK]
theorem isVCovering_of_fpqcCovering (family : ι → Over T)
    (hfamily : Scheme.FpqcCovering family) :
    IsVCovering T (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := sorry

/-- Every fixed-target fppf cover is a `V` cover. -/
@[stacks 0ETK]
theorem isVCovering_of_fppfCover (cover : FppfCover T) :
    IsVCovering T cover.X cover.f := sorry

/-- Every fixed-target syntomic cover is a `V` cover. -/
@[stacks 0ETK]
theorem isVCovering_of_syntomicCover (cover : SyntomicCover T) :
    IsVCovering T cover.X cover.f := sorry

/-- Every smooth-covering indexed family is a `V` cover. -/
@[stacks 0ETK]
theorem isVCovering_of_smoothCovering
    (family : ι → Over T) (hfamily : Scheme.SmoothCovering family) :
    IsVCovering T (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := sorry

/-- Every étale cover is a `V` cover. -/
@[stacks 0ETK]
theorem isVCovering_of_etaleCovering (cover : Scheme.Cover Scheme.etalePrecoverage T) :
    IsVCovering T cover.X cover.f := sorry

/-- Every Zariski open cover is a `V` cover. -/
@[stacks 0ETK]
theorem isVCovering_of_zariskiCovering (cover : T.OpenCover) :
    IsVCovering T cover.X cover.f := sorry

/-- Every proper-hypercovering family is a `V` cover. -/
@[stacks 0ETK]
theorem isVCovering_of_phCovering {family : ι → Scheme.{u}}
    {map : ∀ i, family i ⟶ T} (hfamily : PhCovering family map) :
    IsVCovering T family map := sorry

/-- A fixed-target family of locally finitely presented scheme morphisms is a
proper-hypercovering family if and only if it is a `V` covering family. -/
theorem phCovering_iff_isVCovering_of_locallyOfFinitePresentation
    {ι : Type v} {T : Scheme.{u}} (family : ι → Scheme.{u})
    (map : ∀ i, family i ⟶ T)
    (hmap : ∀ i, LocallyOfFinitePresentation (map i)) :
    PhCovering family map ↔ IsVCovering T family map := sorry

end AlgebraicGeometry
