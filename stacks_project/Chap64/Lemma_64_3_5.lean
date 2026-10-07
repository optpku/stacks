module

public import stacks_project.Chap64.Lemma_64_3_5_Pullback
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.SchemeOverField

/- Lemma 64.3.5 (1): for a sheaf F on X_étale there is a canonical isomorphism
π_X⁻¹ F ≅ F, induced by the small-étale site isomorphism of geometric
Frobenius. -/
@[stacks 03SR] #check geometricFrobeniusSheafIso

/- Lemma 64.3.5 (2): for a sheaf F on X_étale there is a canonical isomorphism
F ≅ (π_X)_* F, induced by restriction along the inverse of the comparison
γ_U = (U.hom, F_U^f). -/
@[stacks 03SR] #check geometricFrobeniusSheafPushforwardIso
