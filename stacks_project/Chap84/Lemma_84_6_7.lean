module

public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap84.Lemma_84_6_7_Comparison
public import stacks_project.Chap84.Lemma_84_6_7_InverseImage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 84.6.7

In the setup of Lemma 84.6.4, if `f : X ⟶ Y` is flat, locally of finite
presentation, and surjective, then the functor from sheaves on `Y_étale` to
the iso-comma of `a_X⁻¹` and `f_big,fppf⁻¹`, sending `ℱ` to
`(f_small⁻¹ ℱ, a_Y⁻¹ ℱ, can)`, is an equivalence. Printed sheaves on
`(Sch/Y)_fppf` are the Lemma 84.3.1 view of sheaves on `(Spaces/Y)_fppf`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale
namespace SmallToBig

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable [HasSheafify (smallEtaleTopology X) (Type (u + 1))]
variable [HasSheafify (smallEtaleTopology Y) (Type (u + 1))]

/-- Lemma 84.6.7: if `f : X ⟶ Y` is flat, locally of finite presentation, and
surjective, then the functor `fppfSmallIsoCommaFunctor f` from sheaves on
`Y_étale` to the iso-comma of `a_X⁻¹` and `f_big,fppf⁻¹`, sending `ℱ` to
`(f_small⁻¹ ℱ, a_Y⁻¹ ℱ, can)`, is an equivalence. Printed `ℋ ∈ Sh((Sch/Y)_fppf)`
is the Lemma 84.3.1 view of `ℋ ∈ Sh((Spaces/Y)_fppf)` after étale localization
to a scheme. -/
@[stacks 0DGL]
noncomputable instance fppfSmallIsoCommaFunctor_isEquivalence
    [Flat f] [LocallyOfFinitePresentation f] [Surjective f] :
    (fppfSmallIsoCommaFunctor f).IsEquivalence := sorry

end SmallToBig
end AlgebraicGeometry.AlgebraicSpace.Etale

end

end
