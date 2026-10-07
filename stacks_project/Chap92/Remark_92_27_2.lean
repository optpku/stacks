module

public import stacks_project.Chap92.Remark_92_27_2_Affine
public import stacks_project.Chap92.Remark_92_27_2_Evaluation
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

/-!
# Standard affine resolutions and `Lπ_!` on algebraic spaces

Remark 92.27.2 records the functorial standard affine object `A_{•,U}` in the fibre of
`C_{X/Λ}` over an étale `U`, the pointlike mapping-space hypothesis of Lemma 21.39.7, and
the computation of `Lπ_!(F)` by evaluating an abelian sheaf `F` on `A_{•,U}`.
-/

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.Cotangent

/- Remark 92.27.2 (1): for `U` in `X_étale`, the standard polynomial resolution of `𝒪_X(U)`
over `Λ` yields the functorial cosimplicial object `A_{•,U}` of the fibre of `C_{X/Λ}` over
`U`, with `A_{n,U} = Spec(P_{n,U})`. -/
@[stacks 08VL]
#check standardAffine

/- Remark 92.27.2 (2): `A_{•,U}` is a cosimplicial object of the fibre as in Cohomology on
Sites, Lemma 21.39.7. -/
@[stacks 08VL]
#check standardAffine_hasHomSpaces

/- Remark 92.27.2 (3): for an abelian sheaf `F` on `C_{X/Λ}`, the cohomology of the
presheaf complex `U ↦ F(A_{•,U})` computes the homology of `F` on the fibre category. -/
@[stacks 08VL]
#check eval_homology_iso

/- Remark 92.27.2 (4): sheafification of that homology computes `L_n π_!(F)`, by Cohomology
on Sites, Lemma 21.40.2. -/
@[stacks 08VL]
#check sheafify_iso_lowerShriek

/- Remark 92.27.2 (5): equivalently, the complex of sheaves whose term in degree `-n` is the
sheafification of `U ↦ F(A_{n,U})` computes `Lπ_!(F)`. -/
@[stacks 08VL]
#check evalSheafComplex_iso
