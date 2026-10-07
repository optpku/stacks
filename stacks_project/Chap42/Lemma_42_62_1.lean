module

public import stacks_project.Chap42.Lemma_42_62_1_IntersectionProduct
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules hiding dual

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.Total

variable {k : Type u} [Field k]

/-- Lemma 42.62.1: The product defined above is associative. More precisely, let `k` be a
field, let `X` be smooth over `k`, let `Y`, `Z`, `W` be schemes locally of finite type over
`X`, and let `alpha` be in `CH_*(Y)`, `beta` in `CH_*(Z)`, `gamma` in `CH_*(W)`. Then
`(alpha · beta) · gamma = alpha · (beta · gamma)` in `CH_*(Y ×_X Z ×_X W)`. -/
@[stacks 0FC1]
theorem intersectionProductOver_assoc
    (X : SchemeOverField k) [Smooth X.hom] {Y Z W : SchemeOverField k}
    (fY : Y ⟶ X) (fZ : Z ⟶ X) (fW : W ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType W.hom]
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left] [LocallyOfFiniteType fW.left]
    (r : ℕ) [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r)
    (alpha : Total (fun _ ↦ 0) Y) (beta : Total (fun _ ↦ 0) Z)
    (gamma : Total (fun _ ↦ 0) W) :
    map (fun _ ↦ 0) (pullbackAssoc fY fZ fZ fW).hom
        (intersectionProductOver X (pullback.snd fY fZ ≫ fZ) fW r D
          (intersectionProductOver X fY fZ r D alpha beta) gamma) =
      intersectionProductOver X fY (pullback.fst fZ fW ≫ fZ) r D alpha
        (intersectionProductOver X fZ fW r D beta gamma) := sorry

end AlgebraicGeometry.ChowGroup.Total
