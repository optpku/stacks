module

public import ReasLib.Algebra.Category.ModuleCat.FiniteProjective.Resolution
public import ReasLib.Algebra.Category.ModuleCat.ProjectiveResolution.Coordinate.Syzygy
import StacksCheckRecall

/-!
# Projective Dimension and Finite-Projective Resolutions

@stack 0CXE
-/

@[expose] public section

/- Lemma 10.109.6 (0CXE): for a finite module over a Noetherian ring, the four
projective-dimension conditions of Lemma 10.109.4 are also equivalent to the existence of a
resolution
`0 ⟶ P d ⟶ P (d - 1) ⟶ ⋯ ⟶ P 0 ⟶ M ⟶ 0`
whose terms are finite projective modules. -/
@[stacks 0CXE "(1)-(4), projective-resolution core"]
#check @CategoryTheory.ModuleCat.ProjectiveResolution.Coordinate.projectiveDimensionLE_tfae_kernelSyzygy

@[stacks 0CXE "(1) iff (5), bounded finite-projective resolution"]
#check @CategoryTheory.ModuleCat.FiniteProjective.hasProjectiveDimensionLE_iff_hasResolutionLE
