/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_100_4_Comparison
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace SmallToBig

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasSheafify X.smallEtaleTopology (Type (u + 1))]
variable [HasSheafify Y.smallEtaleTopology (Type (u + 1))]

/-- Lemma 59.100.4: if `f : X ⟶ Y` is flat, locally of finite presentation, and
surjective, then the functor `fppfSmallIsoCommaFunctor f` from sheaves on
`Y.smallEtaleTopology` to the iso-comma of `a_X⁻¹` and `f_big,fppf⁻¹`, sending
`ℱ` to `(f_small⁻¹ ℱ, a_Y⁻¹ ℱ, can)`, is an equivalence. -/
@[stacks 0DEU]
noncomputable instance fppfSmallIsoCommaFunctor_isEquivalence
    [Flat f] [LocallyOfFinitePresentation f] [Surjective f] :
    (fppfSmallIsoCommaFunctor f).IsEquivalence := sorry

end SmallToBig
end AlgebraicGeometry.Scheme.Etale

end

end
