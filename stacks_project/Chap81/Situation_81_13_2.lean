/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProperIsoOverComplement
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
import StacksCheckRecall

open AlgebraicGeometry AlgebraicSpace CategoryTheory

universe u

/- Situation 81.13.2: A proper morphism is an isomorphism over the open complement
of a closed immersion. -/
@[stacks 0AGH] #check (AlgebraicGeometry.AlgebraicSpace.IsProperIsoOverComplement :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X' X Z : AlgebraicGeometry.AlgebraicSpace S} (f : X' ⟶ X) (i : Z ⟶ X),
    ∀ [AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion i], Prop)

section

variable {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X]
variable {Z X' : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] (f : X' ⟶ X)

/- Situation 81.13.2 (1): `X` is a locally Noetherian algebraic space over `S`. -/
@[stacks 0AGH] #check (X : AlgebraicSpace S)
#check (inferInstance : IsLocallyNoetherian X)

/- Situation 81.13.2 (2): `i : Z ⟶ X` is a closed immersion. -/
@[stacks 0AGH] #check (i : Z ⟶ X)
#check (inferInstance : IsClosedImmersion i)

/- Situation 81.13.2 (3): `U ⊂ X` is the complementary open subspace of `i`. -/
@[stacks 0AGH] #check (closedImmersionComplement i : AlgebraicSpace S)
#check (closedImmersionComplementSubspace i : OpenSubspace X)

end
