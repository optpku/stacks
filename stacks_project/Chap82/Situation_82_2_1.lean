module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.UniversallyCatenary
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Transfer

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

section

variable {S : Scheme.{u}} (B : AlgebraicSpace S)
  [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
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
@[stacks 0EDT] #check (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} (f : X ⟶ B) [LocallyOfFiniteType f]
    (δ : Points B → ℤ), Points X → ℤ)

#check (inferInstance : UniversallyCatenary B)
#check (inferInstance : IsAbsolutelyQuasiSeparated B)
#check (inferInstance : IsLocallyNoetherian B)
#check (inferInstance : IsQuasiSeparated B)
#check (δ : Points B → ℤ)
#check (inferInstance : IsDimensionFunction δ)
#check (inferInstance : QuasiSeparated f)
#check (inferInstance : LocallyOfFiniteType f)
#check (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction f δ : Points X → ℤ)
#check (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated.of_quasiSeparated f :
  IsAbsolutelyQuasiSeparated X)
#check (AlgebraicGeometry.AlgebraicSpace.IsQuasiSeparated.of_quasiSeparated f :
  IsQuasiSeparated X)
#check (AlgebraicGeometry.AlgebraicSpace.instIsDecent_of_isQuasiSeparated :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsQuasiSeparated X], IsDecent X)
#check (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction_apply :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} (f : X ⟶ B) [LocallyOfFiniteType f]
    (δ : Points B → ℤ) (x : Points X),
    AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction f δ x =
      δ (Points.map f x) + (residueFieldTrdegAt f x : ℤ))
#check (AlgebraicGeometry.AlgebraicSpace.Hom.instIsDimensionFunction_relativeDimensionFunction :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
    (f : X ⟶ B) [IsDecent X] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ],
    IsDimensionFunction (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction f δ))

end
