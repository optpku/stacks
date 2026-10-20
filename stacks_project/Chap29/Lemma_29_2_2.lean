module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Factorization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Z Z' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X)
  [IsClosedImmersion i] [IsClosedImmersion i']
variable (a : Z ⟶ Z')

/- Lemma 29.2.2 (1): a closed immersion factors through another closed immersion exactly when
the latter's kernel ideal sheaf is contained in the former's kernel ideal sheaf. -/
@[stacks 01QP] #check
  (AlgebraicGeometry.IsClosedImmersion.exists_lift_iff_ker_le i' i :
    (∃ a : Z ⟶ Z', a ≫ i' = i) ↔ i'.ker ≤ i.ker)

/- Lemma 29.2.2 (2): a factor map between closed immersions is a closed immersion. -/
@[stacks 01QP] #check
  (AlgebraicGeometry.IsClosedImmersion.of_comp_eq a i' i :
    a ≫ i' = i → IsClosedImmersion a)

/- Lemma 29.2.2 (3): two closed immersions are isomorphic over their target exactly when their
kernel ideal sheaves are equal. -/
@[stacks 01QP] #check
  (AlgebraicGeometry.IsClosedImmersion.overIso_iff_ker_eq i i' :
    Nonempty (Over.mk i ≅ Over.mk i') ↔ i.ker = i'.ker)

end AlgebraicGeometry
