/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import stacks_project.Chap76.Lemma_76_32_2
import stacks_project.Chap67.Definition_67_4_2_Separation
import stacks_project.Chap65.Definition_65_13_2_Separation

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

section

variable {S : Scheme.{u}} (B : AlgebraicSpace S)
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable {X : AlgebraicSpace S} (f : X ⟶ B)
  [QuasiSeparated f] [LocallyOfFiniteType f]

/- Situation 82.2.1: `S` is a scheme and `B` is an algebraic space over `S`.
We assume `B` is quasi-separated, locally Noetherian, and universally catenary,
and we are given a dimension function `δ : Points B → ℤ`. An algebraic space
`X` over `B` is good when the structure morphism `f : X ⟶ B` is quasi-separated
and locally of finite type. Then `δ_{X/B}` is `f.relativeDimensionFunction δ`,
sending `x` to `δ (Points.map f x)` plus the transcendence degree of `x / f(x)`,
and this is a dimension function by Lemma 76.32.2. -/
@[stacks 0EDT] #check (UniversallyCatenary B : Prop)

#check (inferInstance : IsLocallyNoetherian B)
#check (inferInstance : IsQuasiSeparated B)
#check (δ : Points B → ℤ)
#check (inferInstance : IsDimensionFunction δ)
#check (inferInstance : QuasiSeparated f)
#check (inferInstance : LocallyOfFiniteType f)
#check (f.relativeDimensionFunction δ : Points X → ℤ)
#check Hom.relativeDimensionFunction_apply
#check Hom.instIsDimensionFunction_relativeDimensionFunction

end
