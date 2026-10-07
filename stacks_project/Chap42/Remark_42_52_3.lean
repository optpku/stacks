module

import StacksCheckRecall
import stacks_project.Chap42.Remark_42_52_3_CutoffChern

/- Remark 42.52.3: In Situation 42.50.1, the mixed series
c⁽ᵖ⁾(Z ⟶ X, E) = 1 + c₁(E) + ⋯ + c_{p-1}(E) + c_p(Z ⟶ X, E) + c_{p+1}(Z ⟶ X, E) + ⋯
is the cutoff-valued family in A⁽ᵖ⁾(Z ⟶ X) with ambient Chern classes of E in
degrees n < p and localized Chern classes along Z ⟶ X in degrees n ≥ p. -/
@[stacks 0FBC] #check AlgebraicGeometry.LocalizedChern.mixedChernClass
