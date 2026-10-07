module

public import stacks_project.Chap76.Lemma_76_7_8_Transitivity
import StacksCheckRecall

/-!
# Transitivity sequence for relative differentials of algebraic spaces

For composable morphisms of algebraic spaces over a scheme `S`, the comparison maps of
Lemma 76.7.6 assemble into a canonical exact sequence
`(Modules.pullback f).obj (relativeDifferentials g) ⟶ relativeDifferentials (f ≫ g) ⟶
relativeDifferentials f ⟶ 0`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Hom.Differentials
open AlgebraicGeometry.AlgebraicSpace.Hom.Differentials.Transitivity

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {X Y B : AlgebraicSpace S}
variable (f : X ⟶ Y) (g : Y ⟶ B)

/- Lemma 76.7.8: for morphisms `f : X ⟶ Y` and `g : Y ⟶ B` of algebraic spaces over a
scheme `S`, the canonical sequence
`(Modules.pullback f).obj (relativeDifferentials g) ⟶ relativeDifferentials (f ≫ g) ⟶
relativeDifferentials f ⟶ 0` is exact. -/
@[stacks 05Z8] #check (exact_and_epi f g :
  (complex f g).Exact ∧ Epi (projection f g))

/- The reusable owner supplies the canonical short complex as concrete data. -/
@[stacks 05Z8] #check (complex f g : ShortComplex X.Modules)

/- The left map is the comparison of the identity square on `B`. -/
@[stacks 05Z8] #check (baseChange f g :
  (Modules.pullback f).obj (relativeDifferentials g) ⟶ relativeDifferentials (f ≫ g))

/- The right map is identity-pullback transport of the comparison of the identity square
on `X`. -/
@[stacks 05Z8] #check (projection f g :
  relativeDifferentials (f ≫ g) ⟶ relativeDifferentials f)
