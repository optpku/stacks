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
# Projective Dimension and Finite Free Resolutions

@stack 0CXF
-/

@[expose] public section

/- Lemma 10.109.7 (0CXF): for a finite module over a local Noetherian ring, the four
projective-dimension conditions of Lemma 10.109.4, the free-resolution condition of Lemma
10.109.5, and the finite-projective-resolution condition of Lemma 10.109.6 are also equivalent to
the existence of a finite free resolution
`0 ⟶ F d ⟶ F (d - 1) ⟶ ⋯ ⟶ F 0 ⟶ M ⟶ 0`. -/
@[stacks 0CXF "(1)-(4), projective-resolution core"]
#check @CategoryTheory.ModuleCat.ProjectiveResolution.Coordinate.projectiveDimensionLE_tfae_kernelSyzygy

@[stacks 0CXF "(1) iff (5), bounded free resolution"]
#check @ChainComplex.FreeResolution.hasProjectiveDimensionLE_iff_hasLengthLE

@[stacks 0CXF "(1) iff (6), bounded finite-projective resolution"]
#check @CategoryTheory.ModuleCat.FiniteProjective.hasProjectiveDimensionLE_iff_hasResolutionLE

@[stacks 0CXF "(1) iff (7), bounded finite-free resolution"]
#check @ChainComplex.FiniteFreeResolution.hasProjectiveDimensionLE_iff_hasLengthLE
