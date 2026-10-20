/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ProjectiveResolution.Coordinate.Syzygy
public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution.Bounded.LocalRing
import StacksCheckRecall

/-!
# Projective Dimension and Free Resolutions over Local Rings

@stack 0CXD
-/

@[expose] public section

/- Lemma 10.109.5 (0CXD): over a local ring, the four projective-dimension conditions
of Lemma 10.109.4 are also equivalent to the existence of a free resolution
`0 ⟶ P d ⟶ P (d - 1) ⟶ ⋯ ⟶ P 0 ⟶ M ⟶ 0`.

The five clauses respectively record the projective-dimension bound, a bounded projective
resolution, a projective `d`th syzygy for some resolution, the same condition for every
resolution, and a bounded free resolution. -/
@[stacks 0CXD "(1)-(4), projective-resolution core"]
#check @CategoryTheory.ModuleCat.ProjectiveResolution.Coordinate.projectiveDimensionLE_tfae_kernelSyzygy

@[stacks 0CXD "(1) iff (5), bounded free resolution"]
#check @ChainComplex.FreeResolution.hasProjectiveDimensionLE_iff_hasLengthLE
