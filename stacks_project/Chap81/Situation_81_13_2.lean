module

public import stacks_project.Chap81.Situation_81_13_2_ProperIsoOverComplement
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
import StacksCheckRecall

open AlgebraicGeometry AlgebraicSpace CategoryTheory

universe u

section

variable {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X]
variable {Z X' : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] (f : X' ⟶ X)

/- Situation 81.13.2 (1): `X` is a locally Noetherian algebraic space over `S`. -/
@[stacks 0AGH] #check (X : AlgebraicSpace S)
@[stacks 0AGH] #check (inferInstance : IsLocallyNoetherian X)

/- Situation 81.13.2 (2): `i : Z ⟶ X` is a closed immersion. -/
@[stacks 0AGH] #check (i : Z ⟶ X)
@[stacks 0AGH] #check (inferInstance : IsClosedImmersion i)

/- Situation 81.13.2 (3): `U ⊂ X` is the complementary open subspace of `i`. -/
@[stacks 0AGH] #check (closedImmersionComplement i : AlgebraicSpace S)
@[stacks 0AGH] #check (closedImmersionComplementSubspace i : OpenSubspace X)

/- Situation 81.13.2 (4): `f : X' ⟶ X` is proper and `f⁻¹U ⟶ U` is an isomorphism. -/
@[stacks 0AGH] #check (IsProperIsoOverComplement f i : Prop)

end
