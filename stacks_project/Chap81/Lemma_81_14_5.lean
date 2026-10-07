module

public import stacks_project.Chap81.Lemma_81_14_5_Comparison

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 81.14.5: let `S` be a scheme, let `X ⟶ B` and `Y ⟶ B` be morphisms of
algebraic spaces over `S`, let `U ⊂ X` be an open subspace, and let
`q : V ⟶ X ×_B Y` be a quasi-compact morphism whose composition with the first
projection maps into `U`. If `b : X' ⟶ X` is a `U`-admissible blowup with
center `center`, then the scheme-theoretic image of the induced morphism
`V ⟶ X' ×_B Y` is the strict transform of the scheme-theoretic image of `q`,
as closed immersions into `X' ×_B Y`. -/
@[stacks 0F49]
theorem image_liftAdmissible_isomorphic_strictTransform
    {S : Scheme.{u}} {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (U : OpenSubspace X) (b : X' ⟶ X) (center : ClosedSubspace X)
    [IsAdmissibleBlowupCenter U b center]
    (qU : V ⟶ U.X) (hqU : qU ≫ U.ι = q ≫ pullback.fst f g) :
    Nonempty
      (Over.mk (liftAdmissibleImageι f g q U b qU
          (isIso_pullbackFst_of_isAdmissibleBlowupCenter U b center) hqU) ≅
        Over.mk (strictTransformImageMap f g q b center)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
