/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.Determinant.Projective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.119.6

The reusable owner of the finite-projective determinant and the Weinstein–Aronszajn identity is
`ReasLib.LinearAlgebra.Determinant.Projective`. The split finite-free presentation is explicit data
there, while presentation independence is exposed as a theorem rather than hidden in downstream
proofs.

@stack 0FJF
-/

/- Lemma 15.119.6: `det(1 + a ∘ₗ b) = det(1 + b ∘ₗ a)` for finite-projective modules. -/
@[stacks 0FJF "Lemma 15.119.6: finite-projective determinant identity"]
#check @LinearMap.projectiveDet_id_add_comp

#check @LinearMap.SplitFreePresentation
#check @LinearMap.splitFreePresentation
#check @LinearMap.projectiveDet
#check @LinearMap.det_lift_independent
#check @LinearMap.projectiveDet_of_presentation
#check @LinearMap.projectiveDet_eq_det_of_free

end
