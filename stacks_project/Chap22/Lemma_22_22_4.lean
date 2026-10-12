/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Limits
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, w} R) (J : Type v)
variable (M : J → DifferentialGradedModule.{u, v} A)

/- Lemma 22.22.4 (09QI) (1), coproduct part: `DifferentialGradedModule.Derived.Category A`
has coproducts of arbitrary same-universe families. -/
@[stacks 09QI]
#check (inferInstance :
  HasCoproductsOfShape J (DifferentialGradedModule.Derived.Category.{u, v} A))

/- Lemma 22.22.4 (09QI) (2): derived coproducts are represented by degreewise coproducts of
right differential graded `A`-modules. -/
@[stacks 09QI]
#check (inferInstance :
  PreservesColimit (Discrete.functor M)
    (DifferentialGradedModule.Derived.fromModules.{u, v} A))

/- Lemma 22.22.4 (09QI) (1), product part: `DifferentialGradedModule.Derived.Category A`
has products of arbitrary same-universe families. -/
@[stacks 09QI]
#check (inferInstance :
  HasProductsOfShape J (DifferentialGradedModule.Derived.Category.{u, v} A))

/- Lemma 22.22.4 (09QI) (3): derived products are represented by degreewise products of right
differential graded `A`-modules. -/
@[stacks 09QI]
#check (inferInstance :
  PreservesLimit (Discrete.functor M)
    (DifferentialGradedModule.Derived.fromModules.{u, v} A))
