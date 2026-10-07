module

public import stacks_project.Chap76.Lemma_76_44_10_Transitivity
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
variable (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j]

/- Lemma 76.5.6: Let `S` be a scheme. Let `Z ⟶ Y ⟶ X` be immersions of algebraic spaces
over `S`. Then there is a canonical exact sequence
`i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0`,
where the maps are `Hom.Conormal.Transitivity.baseChange` and
`Hom.Conormal.Transitivity.projection` coming from `Hom.Conormal.map` (Lemma 76.5.3)
and `i : Z ⟶ Y` is the first morphism. -/
@[stacks 06BD] #check
  (Hom.Conormal.Transitivity.exact_and_epi i j :
    (Hom.Conormal.Transitivity.complex i j).Exact ∧
      Epi (Hom.Conormal.Transitivity.projection i j))
