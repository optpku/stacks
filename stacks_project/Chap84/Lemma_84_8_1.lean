module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import stacks_project.Chap84.Lemma_84_8_1_InverseImage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 84.8.1

For a sheaf of sets `F` on the small étale site of an algebraic space `X`,
the comparison unit identifies `ε_{X,*} (a_X⁻¹ F)` with `π_X⁻¹ F` and
`a_{X,*} (a_X⁻¹ F)` with `F`. For a locally torsion abelian sheaf, the higher
direct images `R^i ε_{X,*} (a_X⁻¹ F)` vanish for `i > 0`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open AlgebraicGeometry.AlgebraicSpace.PhComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PhComparison

/-- Lemma 84.8.1 (1): for a sheaf of sets `F` on `X_étale`, the comparison unit
identifies `ε_{X,*} (a_X⁻¹ F)` with `π_X⁻¹ F`. -/
@[stacks 0DGT]
theorem epsilon_pushforward_aInverseImage_unit_isIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    IsIso ((epsilon X).adjunction.unit.app (((siteMorphismOfTopoi X)⁻¹).obj F)) := sorry

/-- Lemma 84.8.1 (2): for a sheaf of sets `F` on `X_étale`, the comparison unit
identifies `a_{X,*} (a_X⁻¹ F)` with `F`. -/
@[stacks 0DGT]
theorem toSmallEtale_unit_isIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    IsIso ((toSmallEtale X).adjunction.unit.app F) := sorry

/-- Lemma 84.8.1 (3): for a locally torsion abelian sheaf `F` on `X_étale` and `0 < i`,
the higher direct images `R^i ε_{X,*} (a_X⁻¹ F)` vanish. -/
@[stacks 0DGT]
theorem epsilon_rightDerived_aInverseImage_isZero {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (i : ℕ) (hi : 0 < i) :
    IsZero
      (((comparisonTopologyPushforwardAb etale_le_ph X).rightDerived i).obj
        ((aInverseImage X).obj F)) := sorry

end AlgebraicGeometry.AlgebraicSpace.PhComparison

end

end
