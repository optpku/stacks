module

public import stacks_project.Chap98.Remark_98_9_2_Predeformation
import StacksCheckRecall

/-!
# Formal objects of a category fibred in groupoids as formal objects of `ℱ_{X, k, x₀}`

Stacks tag 0CXH: a scheme-level formal object of `X` over a locally Noetherian
scheme supplies a Chap90 formal object of the predeformation category
`ℱ_{X, R/m, ξ₁}`.
-/

@[expose] public section

open AlgebraicGeometry.GroupoidsOver

/- Remark 98.9.2: if `S` is locally Noetherian, `p : X ⟶ (Sch/S)_fppf` is a
category fibred in groupoids, and `ξ` is a formal object of `X`, then with
`k = ResidueField ξ.base.carrier` and `x0 = ξ.stageOne` the same data is a
formal object of the predeformation category `F_{X, k, x0}` from Section 98.3. -/
@[stacks 0CXH] #check FormalObject.toPredeformation
