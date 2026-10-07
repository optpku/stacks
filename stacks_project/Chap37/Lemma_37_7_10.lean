module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.ConormalSequence
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Thickening.IsUniversalFirstOrder.Differentials

variable {X S : Scheme.{u}} (T : Thickening.Over X) (f : X ⟶ S)
  [FormallyUnramified T.left.hom] [IsUniversalFirstOrder T]

/- Lemma 37.7.10: if `T` is a universal first-order thickening of a formally
unramified morphism `T.left.hom : Z ⟶ X` over `S`, then the canonical sequence
`C_{Z/X} ⟶ T.left.hom^* Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0` is exact, and its first arrow is
induced by `d_{Z'/S}`. -/
@[stacks 04FC] #check
  (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.Differentials.exact_and_epi T f :
    (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.Differentials.complex T f).Exact ∧
      Epi (Scheme.Hom.Conormal.Differentials.comparison T.left.hom f))

#check
  (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.Differentials.conormalMap_comp_pullbackComparison
      T f :
    AlgebraicGeometry.Thickening.IsUniversalFirstOrder.Differentials.conormalMap T f ≫
        AlgebraicGeometry.Thickening.IsUniversalFirstOrder.Differentials.pullbackComparison T f =
      Scheme.Hom.Conormal.Differentials.map T.hom.left (T.right.hom ≫ f))

end AlgebraicGeometry.Thickening.IsUniversalFirstOrder.Differentials
